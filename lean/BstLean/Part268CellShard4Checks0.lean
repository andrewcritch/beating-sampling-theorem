import BstLean.Part268CellShard4Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12450_0 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (84079848783991 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283397897947 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨0, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (84079848783991 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283397897947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_1 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (84044792530669 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141700936089 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨1, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (84044792530669 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141700936089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_2 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (21002440331669 / 25000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570851463357 / 25000000000000 : ℝ))
      (E := (cell12450 ⟨2, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (21002440331669 / 25000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570851463357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_3 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83974755135257 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141704925531 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨3, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83974755135257 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141704925531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_4 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (10492471739981 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283413874189 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨4, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (10492471739981 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283413874189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_5 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (1048810220551 / 1250000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570854468439 / 25000000000000 : ℝ))
      (E := (cell12450 ⟨5, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (1048810220551 / 1250000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570854468439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_6 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83869886271777 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283421858281 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨6, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83869886271777 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283421858281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_7 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (1676699595339 / 2000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (228342583603 / 10000000000000 : ℝ))
      (E := (cell12450 ⟨7, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (1676699595339 / 2000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (228342583603 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_8 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (419000490469 / 500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283429815009 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨8, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (419000490469 / 500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283429815009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_9 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83765241216719 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283433860967 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨9, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83765241216719 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283433860967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_10 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41865204550141 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283437807419 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨10, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41865204550141 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283437807419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_11 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (334782406837 / 400000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283441835599 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨11, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (334782406837 / 400000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283441835599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_12 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (8366081900857 / 10000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570861459111 / 25000000000000 : ℝ))
      (E := (cell12450 ⟨12, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (8366081900857 / 10000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570861459111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_13 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (8362606096337 / 10000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285431227079 / 12500000000000 : ℝ))
      (E := (cell12450 ⟨13, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (8362606096337 / 10000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285431227079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_14 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83591327538961 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (35678966261 / 1562500000000 : ℝ))
      (E := (cell12450 ⟨14, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83591327538961 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (35678966261 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_15 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41778309350417 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (28543222483 / 1250000000000 : ℝ))
      (E := (cell12450 ⟨15, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41778309350417 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (28543222483 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_16 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83521934414661 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (142716363289 / 6250000000000 : ℝ))
      (E := (cell12450 ⟨16, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83521934414661 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (142716363289 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_17 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (8348727464629 / 10000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141732915117 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨17, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (8348727464629 / 10000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141732915117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_18 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (20863159840437 / 25000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283469798709 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨18, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (20863159840437 / 25000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283469798709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_19 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41709014263619 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283473781411 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨19, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41709014263619 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283473781411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12451_0 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (21019958260367 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570816095251 / 25000000000000 : ℝ))
      (E := (cell12451 ⟨0, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (21019958260367 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570816095251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_1 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (84044777118181 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285408545489 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨1, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (84044777118181 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285408545489 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_2 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (21002436560939 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141636177313 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨2, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (21002436560939 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141636177313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_3 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41987370190719 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (142704772657 / 6250000000000 : ℝ))
      (E := (cell12451 ⟨3, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41987370190719 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (142704772657 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_4 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (10492469936833 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141640169401 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨4, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (10492469936833 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141640169401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_5 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83904803547067 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570821087543 / 25000000000000 : ℝ))
      (E := (cell12451 ⟨5, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83904803547067 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570821087543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_6 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (8386987250247 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141644173643 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨6, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (8386987250247 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141644173643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_7 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41917483162443 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285411542301 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨7, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41917483162443 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285411542301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_8 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83800084978519 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285412041443 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨8, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83800084978519 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285412041443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_9 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83765228427759 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141650167223 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨9, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83765228427759 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141650167223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_10 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (40883982733 / 48828125000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141652177307 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨10, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (40883982733 / 48828125000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141652177307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_11 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (16739117914311 / 20000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283308341253 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨11, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (16739117914311 / 20000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283308341253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_12 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (4183040359791 / 5000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570828089839 / 25000000000000 : ℝ))
      (E := (cell12451 ⟨12, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (4183040359791 / 5000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570828089839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_13 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (20906512368777 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283316299491 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨13, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (20906512368777 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283316299491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_14 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (20897829093683 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141660171177 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨14, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (20897829093683 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141660171177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_15 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83556607860183 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283324319857 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨15, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83556607860183 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283324319857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_16 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83521923897133 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141664148013 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨16, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83521923897133 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141664148013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_17 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83487264451433 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283332334731 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨17, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83487264451433 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283332334731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_18 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (8345262948911 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (91333453003 / 4000000000000 : ℝ))
      (E := (cell12451 ⟨18, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (8345262948911 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (91333453003 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_19 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83418018976367 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283340330419 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨19, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83418018976367 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283340330419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12452_0 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (21019954325369 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141565487291 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨0, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (21019954325369 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141565487291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_1 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (16808952341637 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570783741563 / 25000000000000 : ℝ))
      (E := (cell12452 ⟨1, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (16808952341637 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570783741563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_2 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (42004865581643 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283138908689 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨2, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (42004865581643 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283138908689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_3 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (20993681407507 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141571463447 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨3, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (20993681407507 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141571463447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_4 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (10492468133981 / 12500000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (228314691429 / 10000000000000 : ℝ))
      (E := (cell12452 ⟨4, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (10492468133981 / 12500000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (228314691429 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_5 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83904789452381 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283150937551 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨5, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83904789452381 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283150937551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_6 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (1677397174709 / 2000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141577444709 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨6, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (1677397174709 / 2000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141577444709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_7 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83834952885069 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283158893979 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨7, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83834952885069 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283158893979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_8 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (20950017966361 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (285395362667 / 12500000000000 : ℝ))
      (E := (cell12452 ⟨8, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (20950017966361 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (285395362667 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_9 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (16753043128193 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141583459621 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨9, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (16753043128193 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141583459621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_10 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83730384176211 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283170897177 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨10, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83730384176211 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283170897177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_11 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (16739115487189 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283174900359 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨11, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (16739115487189 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283174900359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_12 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41830397692557 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283178877719 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨12, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41830397692557 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283178877719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_13 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83626037988851 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283182894021 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨13, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83626037988851 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283182894021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_14 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83591305212467 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (45663737953 / 2000000000000 : ℝ))
      (E := (cell12452 ⟨14, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83591305212467 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (45663737953 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_15 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (16711319404291 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141595447393 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨15, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (16711319404291 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141595447393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_16 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83521913381489 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283194891363 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨16, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83521913381489 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283194891363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_17 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (4174362712921 / 5000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283198893067 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨17, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (4174362712921 / 5000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283198893067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_18 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (3338104784731 / 4000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283202847139 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨18, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (3338104784731 / 4000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283202847139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_19 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (4170900471363 / 5000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283206875167 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨19, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (4170900471363 / 5000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283206875167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12453_0 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (5254987597751 / 6250000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2282997563111 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨0, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (5254987597751 / 6250000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2282997563111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_1 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (42022373150339 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570750390897 / 25000000000000 : ℝ))
      (E := (cell12453 ⟨1, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (42022373150339 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570750390897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_2 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (42004858042633 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (45660111469 / 2000000000000 : ℝ))
      (E := (cell12453 ⟨2, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (42004858042633 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (45660111469 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_3 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41987355440513 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283009544209 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨3, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41987355440513 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283009544209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_4 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (419698653257 / 500000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (91320541711 / 4000000000000 : ℝ))
      (E := (cell12453 ⟨4, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (419698653257 / 500000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (91320541711 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_5 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83904775360021 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283017520093 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨5, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83904775360021 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283017520093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_6 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (20967461242679 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570755385651 / 25000000000000 : ℝ))
      (E := (cell12453 ⟨6, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (20967461242679 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570755385651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_7 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41917469723749 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283025502743 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨7, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41917469723749 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283025502743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_8 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41900029377287 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283029524387 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨8, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41900029377287 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283029524387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_9 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (5235325178521 / 6250000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141516749683 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨9, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (5235325178521 / 6250000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141516749683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_10 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41865185858681 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283037493129 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨10, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41865185858681 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283037493129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_11 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41847782651209 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283041512919 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨11, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41847782651209 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283041512919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_12 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83660783576453 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141522753833 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨12, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83660783576453 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141522753833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_13 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83626026504597 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456609896809 / 20000000000000 : ℝ))
      (E := (cell12453 ⟨13, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83626026504597 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456609896809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_14 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (16718258810433 / 20000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141526753297 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨14, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (16718258810433 / 20000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141526753297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_15 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83556586184651 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283057523427 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨15, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83556586184651 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283057523427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_16 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83521902867729 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570765370579 / 25000000000000 : ℝ))
      (E := (cell12453 ⟨16, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83521902867729 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570765370579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_17 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (333948976269 / 400000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456613101049 / 20000000000000 : ℝ))
      (E := (cell12453 ⟨17, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (333948976269 / 400000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456613101049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_18 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (20863152437311 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456613896263 / 20000000000000 : ℝ))
      (E := (cell12453 ⟨18, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (20863152437311 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456613896263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_19 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (20854499969979 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456614694777 / 20000000000000 : ℝ))
      (E := (cell12453 ⟨19, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (20854499969979 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456614694777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12454_0 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (84079785829087 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282864204377 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨0, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (84079785829087 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282864204377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_1 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (84044730895661 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141434106863 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨1, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (84044730895661 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141434106863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_2 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (42004850504847 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (9131488933 / 400000000000 : ℝ))
      (E := (cell12454 ⟨2, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (42004850504847 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (9131488933 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_3 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (2624209254201 / 3125000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141438107229 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨3, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (2624209254201 / 3125000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141438107229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_4 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (83939716233319 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (114144011213 / 5000000000000 : ℝ))
      (E := (cell12454 ⟨4, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (83939716233319 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (114144011213 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_5 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (83904761269989 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2853605267 / 125000000000 : ℝ))
      (E := (cell12454 ⟨5, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (83904761269989 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2853605267 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_6 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (20967457802067 / 25000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141444095497 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨6, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (20967457802067 / 25000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141444095497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_7 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (20958731503043 / 25000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (45657844453 / 2000000000000 : ℝ))
      (E := (cell12454 ⟨7, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (20958731503043 / 25000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (45657844453 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_8 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (83800045645909 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282896200697 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨8, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (83800045645909 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282896200697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_9 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (83765190073871 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282900190811 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨9, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (83765190073871 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282900190811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_10 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41865179630319 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282904200489 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨10, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41865179630319 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282904200489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_11 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (2615486036593 / 3125000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282908178933 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨11, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (2615486036593 / 3125000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282908178933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_12 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41830385884917 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282912191133 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨12, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41830385884917 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282912191133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_13 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41813007511173 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141458092871 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨13, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41813007511173 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141458092871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_14 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41795641446913 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282920169187 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨14, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41795641446913 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282920169187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_15 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (8355657534977 / 10000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570731036911 / 25000000000000 : ℝ))
      (E := (cell12454 ⟨15, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (8355657534977 / 10000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570731036911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_16 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (83521892355851 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282928185207 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨16, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (83521892355851 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282928185207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_17 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41743616938961 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282932171267 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨17, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41743616938961 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282932171267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_18 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (16690519976403 / 20000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282936169399 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨18, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (16690519976403 / 20000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282936169399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_19 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (16683598066867 / 20000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570735046201 / 25000000000000 : ℝ))
      (E := (cell12454 ⟨19, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (16683598066867 / 20000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570735046201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12455_0 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (5254985631043 / 6250000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282730956167 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨0, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (5254985631043 / 6250000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282730956167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_1 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (84044715493133 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282734974477 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨1, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (84044715493133 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282734974477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_2 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (8400968593657 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282738945919 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨2, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (8400968593657 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282738945919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_3 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41987340695123 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282742937641 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨3, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41987340695123 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282742937641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_4 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16787940363521 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456549391749 / 20000000000000 : ℝ))
      (E := (cell12455 ⟨4, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16787940363521 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456549391749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_5 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41952373591141 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282750960173 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨5, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41952373591141 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282750960173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_6 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16773963489621 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (57068873761 / 2500000000000 : ℝ))
      (E := (cell12455 ⟨6, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16773963489621 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (57068873761 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_7 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83834912579091 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570689734451 / 25000000000000 : ℝ))
      (E := (cell12455 ⟨7, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83834912579091 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570689734451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_8 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (10475004067431 / 12500000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570690732567 / 25000000000000 : ℝ))
      (E := (cell12455 ⟨8, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (10475004067431 / 12500000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570690732567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_9 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83765177293569 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141383467791 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨9, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83765177293569 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141383467791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_10 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (20932586701509 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141385451611 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨10, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (20932586701509 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141385451611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_11 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (5230971315101 / 6250000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282774898403 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨11, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (5230971315101 / 6250000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282774898403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_12 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83660759965259 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141389464059 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨12, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83660759965259 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141389464059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_13 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41813001771049 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141391441467 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨13, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41813001771049 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141391441467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_14 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (1671825434749 / 2000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570696721357 / 25000000000000 : ℝ))
      (E := (cell12455 ⟨14, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (1671825434749 / 2000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570696721357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_15 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (8355656451681 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282790883713 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨15, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (8355656451681 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282790883713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_16 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16704376369171 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141397441859 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨16, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16704376369171 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141397441859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_17 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83487223690437 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (228279889113 / 10000000000000 : ℝ))
      (E := (cell12455 ⟨17, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83487223690437 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (228279889113 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_18 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83452590016589 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (228280291139 / 10000000000000 : ℝ))
      (E := (cell12455 ⟨18, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83452590016589 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (228280291139 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_19 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83417980790517 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456561378293 / 20000000000000 : ℝ))
      (E := (cell12455 ⟨19, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83417980790517 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456561378293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12456_0 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (42039877183409 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282597760697 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨0, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (42039877183409 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282597760697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_1 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (42022350046547 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (91304069209 / 4000000000000 : ℝ))
      (E := (cell12456 ⟨1, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (42022350046547 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (91304069209 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_2 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (42004835432947 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282605711459 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨2, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (42004835432947 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282605711459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_3 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83974666648467 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (14266310711 / 625000000000 : ℝ))
      (E := (cell12456 ⟨3, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83974666648467 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (14266310711 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_4 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83939687404257 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282613688353 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨4, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83939687404257 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282613688353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_5 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83904733096901 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (228261770191 / 10000000000000 : ℝ))
      (E := (cell12456 ⟨5, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83904733096901 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (228261770191 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_6 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83869803690227 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570655426273 / 25000000000000 : ℝ))
      (E := (cell12456 ⟨6, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83869803690227 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570655426273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_7 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41917449574127 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570656426539 / 25000000000000 : ℝ))
      (E := (cell12456 ⟨7, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41917449574127 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570656426539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_8 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (8380001943519 / 10000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141314856551 / 50000000000000 : ℝ))
      (E := (cell12456 ⟨8, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (8380001943519 / 10000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141314856551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_9 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83765164515431 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570658418921 / 25000000000000 : ℝ))
      (E := (cell12456 ⟨9, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83765164515431 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570658418921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_10 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41865167176779 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456527543473 / 20000000000000 : ℝ))
      (E := (cell12456 ⟨10, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41865167176779 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456527543473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_11 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41847764457169 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (228264167133 / 10000000000000 : ℝ))
      (E := (cell12456 ⟨11, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41847764457169 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (228264167133 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_12 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (3346429926509 / 4000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282645660561 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨12, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (3346429926509 / 4000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282645660561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_13 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (20906498015963 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282649691803 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨13, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (20906498015963 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282649691803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_14 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (20897815145759 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282653655321 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨14, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (20897815145759 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282653655321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_15 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83556553685773 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282657673497 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨15, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83556553685773 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282657673497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_16 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83521871337741 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282661694169 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨16, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83521871337741 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282661694169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_17 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41743606752397 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282665664839 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨17, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41743606752397 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282665664839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_18 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (16690516030593 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282669649083 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨18, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (16690516030593 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282669649083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_19 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83417971248461 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (22826736521 / 1000000000000 : ℝ))
      (E := (cell12456 ⟨19, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83417971248461 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (22826736521 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12457_0 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (21019934659869 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282464560187 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨0, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (21019934659869 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282464560187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_1 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (84044684695543 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141234269391 / 50000000000000 : ℝ))
      (E := (cell12457 ⟨1, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (84044684695543 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141234269391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_2 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (16801931159533 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282472529873 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨2, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (16801931159533 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282472529873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_3 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41987325954547 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282476542819 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨3, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41987325954547 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282476542819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_4 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41969836496637 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456496105769 / 20000000000000 : ℝ))
      (E := (cell12457 ⟨4, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41969836496637 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456496105769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_5 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (20976179753461 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282484554621 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨5, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (20976179753461 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282484554621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_6 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83869789934633 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (28531106411 / 1250000000000 : ℝ))
      (E := (cell12457 ⟨6, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83869789934633 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (28531106411 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_7 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83834885719661 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282492527707 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨7, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83834885719661 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282492527707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_8 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (5237500395821 / 6250000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282496549201 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨8, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (5237500395821 / 6250000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282496549201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_9 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (16753030347891 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282500527113 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨9, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (16753030347891 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282500527113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_10 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83730321903201 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456500905377 / 20000000000000 : ℝ))
      (E := (cell12457 ⟨10, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83730321903201 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456500905377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_11 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83695516789143 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282508497717 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨11, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83695516789143 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282508497717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_12 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83660736362233 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456502500919 / 20000000000000 : ℝ))
      (E := (cell12457 ⟨12, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83660736362233 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456502500919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_13 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83625980587607 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570629124043 / 25000000000000 : ℝ))
      (E := (cell12457 ⟨13, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83625980587607 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570629124043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_14 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41795624715291 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282520536983 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨14, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41795624715291 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282520536983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_15 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83556542856657 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282524517 / 100000000000 : ℝ))
      (E := (cell12457 ⟨15, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83556542856657 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282524517 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_16 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (20880465207877 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570632125061 / 25000000000000 : ℝ))
      (E := (cell12457 ⟨16, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (20880465207877 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570632125061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_17 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (2608975103781 / 3125000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570633123099 / 25000000000000 : ℝ))
      (E := (cell12457 ⟨17, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (2608975103781 / 3125000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570633123099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_18 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41726285145571 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (142658531181 / 6250000000000 : ℝ))
      (E := (cell12457 ⟨18, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41726285145571 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (142658531181 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_19 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41708980854083 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282540466711 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨19, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41708980854083 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282540466711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12458_0 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (84079722914663 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570582867551 / 25000000000000 : ℝ))
      (E := (cell12458 ⟨0, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (84079722914663 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570582867551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_1 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (42022334650239 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570583864489 / 25000000000000 : ℝ))
      (E := (cell12458 ⟨1, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (42022334650239 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570583864489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_2 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (42004820365941 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (142646216187 / 6250000000000 : ℝ))
      (E := (cell12458 ⟨2, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (42004820365941 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (142646216187 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_3 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41987318586063 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141171712409 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨3, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41987318586063 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141171712409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_4 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (5246228661541 / 6250000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282347422341 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨4, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (5246228661541 / 6250000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282347422341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_5 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (10488088116639 / 12500000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282351402497 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨5, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (10488088116639 / 12500000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282351402497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_6 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83869776181323 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (142647214483 / 6250000000000 : ℝ))
      (E := (cell12458 ⟨6, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83869776181323 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (142647214483 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_7 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (8383487229331 / 10000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282359402459 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨7, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (8383487229331 / 10000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282359402459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_8 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (20949998308321 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456472687713 / 20000000000000 : ℝ))
      (E := (cell12458 ⟨8, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (20949998308321 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456472687713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_9 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41882569482821 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (228236743187 / 10000000000000 : ℝ))
      (E := (cell12458 ⟨9, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41882569482821 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (228236743187 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_10 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83730309454967 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141185694899 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨10, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83730309454967 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141185694899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_11 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83695504666029 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141187688781 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨11, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83695504666029 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141187688781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_12 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83660724563783 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282379402151 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨12, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83660724563783 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282379402151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_13 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83625969113363 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282383412219 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨13, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83625969113363 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282383412219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_14 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (8359123828009 / 10000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282387414183 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨14, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (8359123828009 / 10000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282387414183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_15 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41778266014731 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282391414221 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨15, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41778266014731 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282391414221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_16 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (20880462581789 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (22823953601 / 1000000000000 : ℝ))
      (E := (cell12458 ⟨16, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (20880462581789 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (22823953601 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_17 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83487193139031 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282399373799 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨17, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83487193139031 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282399373799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_18 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (1043157005389 / 1250000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (114120170131 / 5000000000000 : ℝ))
      (E := (cell12458 ⟨18, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (1043157005389 / 1250000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (114120170131 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_19 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83417952169633 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (285300924191 / 12500000000000 : ℝ))
      (E := (cell12458 ⟨19, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83417952169633 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (285300924191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12459_0 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (42039853596189 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282198375181 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨0, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (42039853596189 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282198375181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_1 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (84044653907901 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570550593033 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨1, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (84044653907901 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570550593033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_2 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (16801925133709 / 20000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282206383157 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨2, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (16801925133709 / 20000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282206383157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_3 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83974622437563 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282210359759 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨3, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83974622437563 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282210359759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_4 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41969822089201 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570553592211 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨4, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41969822089201 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570553592211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_5 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83904690854703 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (45644367227 / 2000000000000 : ℝ))
      (E := (cell12459 ⟨5, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83904690854703 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (45644367227 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_6 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (10483720303787 / 12500000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570555586447 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨6, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (10483720303787 / 12500000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570555586447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_7 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41917429434601 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141113194181 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨7, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41917429434601 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141113194181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_8 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41899990067817 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570557595299 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨8, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41899990067817 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570557595299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_9 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (8376512619399 / 10000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (456446866393 / 20000000000000 : ℝ))
      (E := (cell12459 ⟨9, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (8376512619399 / 10000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (456446866393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_10 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83730297008853 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (228223836413 / 10000000000000 : ℝ))
      (E := (cell12459 ⟨10, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83730297008853 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (228223836413 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_11 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (20923873136249 / 25000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141121184457 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨11, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (20923873136249 / 25000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141121184457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_12 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83660712767373 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570561588309 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨12, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83660712767373 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570561588309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_13 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (522662235257 / 625000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285281290471 / 12500000000000 : ℝ))
      (E := (cell12459 ⟨13, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (522662235257 / 625000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285281290471 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_14 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41795613565779 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282254345041 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨14, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41795613565779 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282254345041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_15 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83556521204187 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141129153513 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨15, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83556521204187 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141129153513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_16 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (16704367964937 / 20000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141131165951 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨16, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (16704367964937 / 20000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141131165951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_17 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83487182958911 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282266309051 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨17, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83487182958911 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282266309051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_18 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83452550572899 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282270302051 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨18, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83452550572899 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282270302051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_19 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (4170897131643 / 5000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141137158047 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨19, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (4170897131643 / 5000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141137158047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12460_0 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (84079691472619 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (228206539069 / 10000000000000 : ℝ))
      (E := (cell12460 ⟨0, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (84079691472619 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (228206539069 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_1 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (84044638517809 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (228206939693 / 10000000000000 : ℝ))
      (E := (cell12460 ⟨1, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (84044638517809 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (228206939693 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_2 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (84009610607653 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282073360199 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨2, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (84009610607653 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282073360199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_3 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (16794921541081 / 20000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282077347641 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨3, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (16794921541081 / 20000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282077347641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_4 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83939629774513 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141040684177 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨4, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83939629774513 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141040684177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_5 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83904676778617 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (91283414931 / 4000000000000 : ℝ))
      (E := (cell12460 ⟨5, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83904676778617 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (91283414931 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_6 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83869748681551 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282089370911 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨6, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83869748681551 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282089370911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_7 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (10479355680917 / 12500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (28526167119 / 1250000000000 : ℝ))
      (E := (cell12460 ⟨7, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (10479355680917 / 12500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (28526167119 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_8 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41899983520093 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456419475419 / 20000000000000 : ℝ))
      (E := (cell12460 ⟨8, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41899983520093 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456419475419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_9 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83765113424499 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570525335847 / 25000000000000 : ℝ))
      (E := (cell12460 ⟨9, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83765113424499 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570525335847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_10 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83730284564861 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141052666919 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨10, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83730284564861 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141052666919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_11 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (20923870106511 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570527338921 / 25000000000000 : ℝ))
      (E := (cell12460 ⟨11, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (20923870106511 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570527338921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_12 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83660700973003 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (285264169731 / 12500000000000 : ℝ))
      (E := (cell12460 ⟨12, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83660700973003 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (285264169731 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_13 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83625946170877 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282117346999 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨13, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83625946170877 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282117346999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_14 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41795607992493 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456424265911 / 20000000000000 : ℝ))
      (E := (cell12460 ⟨14, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41795607992493 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456424265911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_15 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83556510380831 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (228212531169 / 10000000000000 : ℝ))
      (E := (cell12460 ⟨15, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83556510380831 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (228212531169 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_16 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83521829324093 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (228212929933 / 10000000000000 : ℝ))
      (E := (cell12460 ⟨16, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83521829324093 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (228212929933 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_17 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (8348717278063 / 10000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456426659631 / 20000000000000 : ℝ))
      (E := (cell12460 ⟨17, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (8348717278063 / 10000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456426659631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_18 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83452540716477 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570534328401 / 25000000000000 : ℝ))
      (E := (cell12460 ⟨18, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83452540716477 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570534328401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_19 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83417933097847 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282141292639 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨19, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83417933097847 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282141292639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12461_0 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (84079675755387 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281932401163 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨0, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (84079675755387 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281932401163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_1 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (84044623130203 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570484104183 / 25000000000000 : ℝ))
      (E := (cell12461 ⟨1, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (84044623130203 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570484104183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_2 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (42004797774603 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281940447953 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨2, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (42004797774603 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281940447953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_3 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83974592975651 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281944388469 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨3, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83974592975651 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281944388469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_4 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41969807686493 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570487105219 / 25000000000000 : ℝ))
      (E := (cell12461 ⟨4, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41969807686493 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570487105219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_5 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41952331352427 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281952380373 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨5, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41952331352427 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281952380373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_6 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (5241858433443 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1825565113 / 80000000000 : ℝ))
      (E := (cell12461 ⟨6, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (5241858433443 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1825565113 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_7 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (1309919250433 / 1562500000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1140980201941 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨7, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (1309919250433 / 1562500000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1140980201941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_8 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41899976973469 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281964368293 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨8, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41899976973469 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281964368293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_9 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (5235318791073 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570492102037 / 25000000000000 : ℝ))
      (E := (cell12461 ⟨9, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (5235318791073 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570492102037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_10 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (20932568030747 / 25000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285246551871 / 12500000000000 : ℝ))
      (E := (cell12461 ⟨10, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (20932568030747 / 25000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285246551871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_11 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83695468309171 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281976395921 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨11, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83695468309171 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281976395921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_12 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83660689180673 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570495089481 / 25000000000000 : ℝ))
      (E := (cell12461 ⟨12, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83660689180673 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570495089481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_13 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83625934702633 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (456396873147 / 20000000000000 : ℝ))
      (E := (cell12461 ⟨13, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83625934702633 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (456396873147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_14 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83591204840373 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281988367729 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨14, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83591204840373 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281988367729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_15 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (20889124889849 / 25000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281992370077 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨15, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (20889124889849 / 25000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2281992370077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_16 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83521818825381 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1140998189353 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨16, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83521818825381 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1140998189353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_17 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83487162604189 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282000341111 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨17, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83487162604189 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282000341111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_18 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (2607891589433 / 3125000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141002189537 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨18, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (2607891589433 / 3125000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141002189537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_19 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (16683584712919 / 20000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (456401676279 / 20000000000000 : ℝ))
      (E := (cell12461 ⟨19, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (16683584712919 / 20000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (456401676279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12462_0 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (84079660040681 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (228179952217 / 10000000000000 : ℝ))
      (E := (cell12462 ⟨0, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (84079660040681 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (228179952217 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_1 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (42022303872541 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140901773579 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨1, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (42022303872541 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140901773579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_2 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (84009580493203 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140903765377 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨2, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (84009580493203 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140903765377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_3 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (839745782483 / 1000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140905770049 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨3, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (839745782483 / 1000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140905770049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_4 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41969800486911 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (285226940801 / 12500000000000 : ℝ))
      (E := (cell12462 ⟨4, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41969800486911 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (285226940801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_5 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (20976162158353 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281819498449 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨5, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (20976162158353 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281819498449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_6 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41934860595453 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (71306985083 / 3125000000000 : ℝ))
      (E := (cell12462 ⟨6, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41934860595453 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (71306985083 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_7 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (10479352326291 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281827491451 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨7, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (10479352326291 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281827491451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_8 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83799940855891 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140915735367 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨8, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83799940855891 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140915735367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_9 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41882543945999 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140917734123 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨9, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41882543945999 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140917734123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_10 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (16746051936647 / 20000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281839491479 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨10, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (16746051936647 / 20000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281839491479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_11 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83695456194377 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281843489623 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨11, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83695456194377 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281843489623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_12 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41830338695191 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570461867399 / 25000000000000 : ℝ))
      (E := (cell12462 ⟨12, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41830338695191 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570461867399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_13 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (20906480809097 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570462874039 / 25000000000000 : ℝ))
      (E := (cell12462 ⟨13, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (20906480809097 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570462874039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_14 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (2089779842443 / 2500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281855459561 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨14, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (2089779842443 / 2500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281855459561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_15 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83556488739879 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570464870547 / 25000000000000 : ℝ))
      (E := (cell12462 ⟨15, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83556488739879 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570464870547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_16 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83521808328547 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281863453711 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨16, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83521808328547 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281863453711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_17 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41743576214793 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281867437921 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨17, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41743576214793 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281867437921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_18 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83452521009033 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140935720127 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨18, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83452521009033 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140935720127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_19 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83417914033101 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281875465903 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨19, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83417914033101 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281875465903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12463_0 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (168159288657 / 200000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285208336991 / 12500000000000 : ℝ))
      (E := (cell12463 ⟨0, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (168159288657 / 200000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285208336991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_1 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (16808918472489 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (142604417037 / 6250000000000 : ℝ))
      (E := (cell12463 ⟨1, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (16808918472489 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (142604417037 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_2 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (21002391359911 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281674666437 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨2, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (21002391359911 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281674666437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_3 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83974563523351 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281678686819 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨3, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83974563523351 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281678686819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_4 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83939586577019 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281682684953 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨4, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83939586577019 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281682684953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_5 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (20976158641073 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281686669603 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨5, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (20976158641073 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281686669603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_6 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41934853724503 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281690649277 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨6, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41934853724503 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281690649277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_7 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (5239675324699 / 6250000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (570423658057 / 25000000000000 : ℝ))
      (E := (cell12463 ⟨7, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (5239675324699 / 6250000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (570423658057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_8 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (20949981941761 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281698626447 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨8, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (20949981941761 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281698626447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_9 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83765075128987 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281702639679 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨9, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83765075128987 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281702639679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_10 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41865123622801 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (228170662139 / 10000000000000 : ℝ))
      (E := (cell12463 ⟨10, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41865123622801 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (228170662139 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_11 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83695444081663 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281710636791 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨11, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83695444081663 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281710636791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_12 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83660665602129 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (5704286587 / 250000000000 : ℝ))
      (E := (cell12463 ⟨12, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83660665602129 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (5704286587 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_13 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41812955886071 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140859311041 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨13, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41812955886071 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140859311041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_14 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (2612224454907 / 3125000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (456344521011 / 20000000000000 : ℝ))
      (E := (cell12463 ⟨14, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (2612224454907 / 3125000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (456344521011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_15 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (2088911948057 / 2500000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140863324013 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨15, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (2088911948057 / 2500000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140863324013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_16 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (10440224729199 / 12500000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140865320333 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨16, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (10440224729199 / 12500000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140865320333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_17 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83487142256823 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285216823573 / 12500000000000 : ℝ))
      (E := (cell12463 ⟨17, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83487142256823 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285216823573 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_18 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83452511158009 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281738613561 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨18, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83452511158009 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281738613561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_19 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83417904503367 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281742604393 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨19, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83417904503367 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281742604393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12464_0 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (84079628618843 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140766932327 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨0, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (84079628618843 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140766932327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_1 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (21011144245573 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570384462711 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨1, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (21011144245573 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570384462711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_2 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (84009550388527 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570385463751 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨2, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (84009550388527 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570385463751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_3 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16794909760161 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (285193235811 / 12500000000000 : ℝ))
      (E := (cell12464 ⟨3, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16794909760161 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (285193235811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_4 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83939572182579 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281549838631 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨4, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83939572182579 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281549838631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_5 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83904620497493 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281553835933 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨5, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83904620497493 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281553835933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_6 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16773938741877 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281557829043 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨6, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16773938741877 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281557829043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_7 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83834791782281 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570390456553 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨7, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83834791782281 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570390456553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_8 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (20949978670099 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456313167087 / 20000000000000 : ℝ))
      (E := (cell12464 ⟨8, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (20949978670099 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456313167087 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_9 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16753012473627 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (45631397289 / 2000000000000 : ℝ))
      (E := (cell12464 ⟨9, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16753012473627 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (45631397289 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_10 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41865117405043 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281573862727 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨10, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41865117405043 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281573862727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_11 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83695431971027 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281577837429 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨11, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83695431971027 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281577837429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_12 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16732130763183 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140790926769 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨12, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16732130763183 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140790926769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_13 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41812950154947 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140792929849 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨13, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41812950154947 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140792929849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_14 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83591171418287 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570397451053 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨14, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83591171418287 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570397451053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_15 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (417782335533 / 500000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570398452363 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨15, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (417782335533 / 500000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570398452363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_16 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16704357468103 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281597823253 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨16, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16704357468103 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281597823253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_17 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83487132085897 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (142600112069 / 6250000000000 : ℝ))
      (E := (cell12464 ⟨17, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83487132085897 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (142600112069 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_18 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (5215781331799 / 6250000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281605840787 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨18, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (5215781331799 / 6250000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281605840787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_19 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83417894975391 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570402449217 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨19, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83417894975391 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570402449217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12465_0 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (8407961291171 / 10000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (28517514299 / 1250000000000 : ℝ))
      (E := (cell12465 ⟨0, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (8407961291171 / 10000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (28517514299 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_1 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (42022280802311 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570351284931 / 25000000000000 : ℝ))
      (E := (cell12465 ⟨1, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (42022280802311 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570351284931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_2 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (21002383834963 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (142588072143 / 6250000000000 : ℝ))
      (E := (cell12465 ⟨2, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (21002383834963 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (142588072143 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_3 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (4198726704033 / 5000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570353284777 / 25000000000000 : ℝ))
      (E := (cell12465 ⟨3, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (4198726704033 / 5000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570353284777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_4 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83939557790499 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456283420641 / 20000000000000 : ℝ))
      (E := (cell12465 ⟨4, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83939557790499 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456283420641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_5 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (41952303216507 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140710556623 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨5, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (41952303216507 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140710556623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_6 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20967419993011 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281425119881 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨6, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20967419993011 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281425119881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_7 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (2619836824113 / 3125000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140714565679 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨7, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (2619836824113 / 3125000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140714565679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_8 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83799901595947 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140716548849 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨8, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83799901595947 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140716548849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_9 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83765049609441 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140718542283 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨9, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83765049609441 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140718542283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_10 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83730222376689 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281441099449 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨10, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83730222376689 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281441099449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_11 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20923854965617 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281445091537 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨11, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20923854965617 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281445091537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_12 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83660642031739 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140724533871 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨12, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83660642031739 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140724533871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_13 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83625888849643 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140726546411 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨13, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83625888849643 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140726546411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_14 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83591160281507 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (285182132129 / 12500000000000 : ℝ))
      (E := (cell12465 ⟨14, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83591160281507 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (285182132129 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_15 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20889114073209 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456292216549 / 20000000000000 : ℝ))
      (E := (cell12465 ⟨15, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20889114073209 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456292216549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_16 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20880444212329 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281465059631 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨16, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20880444212329 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281465059631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_17 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83487121916809 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281469051481 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨17, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83487121916809 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281469051481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_18 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20863122865339 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (142592066483 / 6250000000000 : ℝ))
      (E := (cell12465 ⟨18, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20863122865339 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (142592066483 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_19 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83417885449173 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281477043329 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨19, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83417885449173 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281477043329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12466_0 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (84079597207101 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140634237971 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨0, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (84079597207101 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140634237971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_1 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (42022273114717 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140636211809 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨1, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (42022273114717 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140636211809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_2 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (84009520293619 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281276448627 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨2, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (84009520293619 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281276448627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_3 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (20993629840729 / 25000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (57032011117 / 2500000000000 : ℝ))
      (E := (cell12466 ⟨3, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (20993629840729 / 25000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (57032011117 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_4 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83939543400779 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570321105199 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨4, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83939543400779 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570321105199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_5 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (16780918474171 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281288443643 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨5, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (16780918474171 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281288443643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_6 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (41934833118491 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281292405941 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨6, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (41934833118491 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281292405941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_7 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (8383476496319 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281296431767 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨7, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (8383476496319 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281296431767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_8 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (2618746516053 / 3125000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281300413239 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨8, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (2618746516053 / 3125000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281300413239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_9 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (16753007370581 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281304416021 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨9, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (16753007370581 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281304416021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_10 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (8373020994541 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281308389577 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨10, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (8373020994541 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281308389577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_11 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83695407755987 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570328099779 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨11, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83695407755987 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570328099779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_12 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83660630249599 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (142582274597 / 6250000000000 : ℝ))
      (E := (cell12466 ⟨12, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83660630249599 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (142582274597 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_13 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83625877391389 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570330094887 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨13, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83625877391389 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570330094887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_14 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (20897787286671 / 25000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281324421633 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨14, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (20897787286671 / 25000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281324421633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_15 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (8355644548099 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (285166051221 / 12500000000000 : ℝ))
      (E := (cell12466 ⟨15, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (8355644548099 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (285166051221 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_16 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83521766359993 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281332407967 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨16, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83521766359993 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281332407967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_17 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (41743555874779 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140668181859 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨17, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (41743555874779 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140668181859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_18 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (3338099264629 / 4000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281340398801 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨18, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (3338099264629 / 4000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281340398801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_19 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (10427234490589 / 12500000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (228134440201 / 10000000000000 : ℝ))
      (E := (cell12466 ⟨19, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (10427234490589 / 12500000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (228134440201 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12467_0 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (42039790752507 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456227160587 / 20000000000000 : ℝ))
      (E := (cell12467 ⟨0, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (42039790752507 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456227160587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_1 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (10505566357091 / 12500000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281139818143 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨1, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (10505566357091 / 12500000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281139818143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_2 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (21002376312457 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281143795853 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨2, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (21002376312457 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281143795853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_3 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83974504647573 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570286950801 / 25000000000000 : ℝ))
      (E := (cell12467 ⟨3, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83974504647573 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570286950801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_4 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83939529013419 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140575895703 / 50000000000000 : ℝ))
      (E := (cell12467 ⟨4, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83939529013419 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140575895703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_5 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (16780915662203 / 20000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281155769219 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨5, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (16780915662203 / 20000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281155769219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_6 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83869652504199 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (91246392123 / 4000000000000 : ℝ))
      (E := (cell12467 ⟨6, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83869652504199 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (91246392123 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_7 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41917375778501 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (228116378539 / 10000000000000 : ℝ))
      (E := (cell12467 ⟨7, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41917375778501 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (228116378539 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_8 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41899937716821 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281167782059 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨8, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41899937716821 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281167782059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_9 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41882512049263 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281171800819 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨9, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41882512049263 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281171800819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_10 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83730197516247 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456235158227 / 20000000000000 : ℝ))
      (E := (cell12467 ⟨10, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83730197516247 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456235158227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_11 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83695395651583 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (285147470021 / 12500000000000 : ℝ))
      (E := (cell12467 ⟨11, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83695395651583 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (285147470021 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_12 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (10457577308687 / 12500000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281183772899 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨12, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (10457577308687 / 12500000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281183772899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_13 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (20906466483783 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140593888983 / 50000000000000 : ℝ))
      (E := (cell12467 ⟨13, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (20906466483783 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140593888983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_14 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41795569006909 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456238356357 / 20000000000000 : ℝ))
      (E := (cell12467 ⟨14, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41795569006909 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456238356357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_15 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (4177821733553 / 5000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456239146477 / 20000000000000 : ℝ))
      (E := (cell12467 ⟨15, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (4177821733553 / 5000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456239146477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_16 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83521755872547 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (8910936531 / 390625000000 : ℝ))
      (E := (cell12467 ⟨16, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83521755872547 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (8910936531 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_17 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (5217943849009 / 6250000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140601864907 / 50000000000000 : ℝ))
      (E := (cell12467 ⟨17, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (5217943849009 / 6250000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140601864907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_18 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83452471771891 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281207729589 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨18, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83452471771891 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281207729589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_19 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83417866402009 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (71287867389 / 3125000000000 : ℝ))
      (E := (cell12467 ⟨19, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83417866402009 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (71287867389 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12468_0 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (84079565805449 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281003240473 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨0, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (84079565805449 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281003240473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_1 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (10505564435813 / 12500000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140503603841 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨1, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (10505564435813 / 12500000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140503603841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_2 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (21002372552119 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281011195969 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨2, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (21002372552119 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281011195969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_3 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83974489934629 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281015214683 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨3, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83974489934629 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281015214683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_4 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41969757314209 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456203843007 / 20000000000000 : ℝ))
      (E := (cell12468 ⟨4, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41969757314209 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456203843007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_5 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83904564253493 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281023205783 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨5, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83904564253493 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281023205783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_6 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41934819386847 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (285128399429 / 12500000000000 : ℝ))
      (E := (cell12468 ⟨6, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41934819386847 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (285128399429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_7 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (20958684538263 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140515596113 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨7, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (20958684538263 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140515596113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_8 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41899931177893 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140517602079 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨8, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41899931177893 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140517602079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_9 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (16753002269261 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570259795241 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨9, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (16753002269261 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570259795241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_10 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83730185089201 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281043188081 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨10, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83730185089201 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281043188081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_11 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (16739076709851 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456209434939 / 20000000000000 : ℝ))
      (E := (cell12468 ⟨11, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (16739076709851 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456209434939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_12 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83660606691429 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (285131400723 / 12500000000000 : ℝ))
      (E := (cell12468 ⟨12, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83660606691429 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (285131400723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_13 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83625854480871 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281055171897 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨13, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83625854480871 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281055171897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_14 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83591126882907 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281059195607 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨14, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83591126882907 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281059195607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_15 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83556423863047 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281063166871 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨15, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83556423863047 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281063166871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_16 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83521745386977 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140533574851 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨16, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83521745386977 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140533574851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_17 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (16697418284113 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570267787443 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨17, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (16697418284113 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570267787443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_18 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41726230964927 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281075172511 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨18, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41726230964927 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281075172511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_19 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41708928440531 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (18248633319 / 800000000000 : ℝ))
      (E := (cell12468 ⟨19, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41708928440531 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (18248633319 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12469_0 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (42039775054203 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456174134597 / 20000000000000 : ℝ))
      (E := (cell12469 ⟨0, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (42039775054203 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456174134597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_1 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (2101112502969 / 2500000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280874707857 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨1, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (2101112502969 / 2500000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280874707857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_2 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (16801895033913 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280878706809 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨2, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (16801895033913 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280878706809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_3 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (16794895044817 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140441339559 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨3, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (16794895044817 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140441339559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_4 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (5246218765361 / 6250000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456177338337 / 20000000000000 : ℝ))
      (E := (cell12469 ⟨4, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (5246218765361 / 6250000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456177338337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_5 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83904550198289 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456178139087 / 20000000000000 : ℝ))
      (E := (cell12469 ⟨5, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83904550198289 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456178139087 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_6 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41934812522733 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280894640941 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨6, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41934812522733 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280894640941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_7 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41917362375669 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280898652281 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨7, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41917362375669 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280898652281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_8 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41899924640063 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280902679539 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨8, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41899924640063 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280902679539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_9 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83764998596239 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140453336227 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨9, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83764998596239 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140453336227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_10 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83730172664271 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280910638439 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨10, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83730172664271 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280910638439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_11 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83695371449003 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280914642697 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨11, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83695371449003 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280914642697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_12 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41830297457699 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280918634143 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨12, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41830297457699 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280918634143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_13 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (16725168605721 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140461309717 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨13, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (16725168605721 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140461309717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_14 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (2612222367311 / 3125000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140463331549 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨14, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (2612222367311 / 3125000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140463331549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_15 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (20889103264237 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280930655093 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨15, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (20889103264237 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280930655093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_16 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83521734903283 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (570233664857 / 25000000000000 : ℝ))
      (E := (cell12469 ⟨16, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83521734903283 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (570233664857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_17 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83487081258823 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280938623593 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨17, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83487081258823 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280938623593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_18 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83452452089613 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (142558913197 / 6250000000000 : ℝ))
      (E := (cell12469 ⟨18, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83452452089613 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (142558913197 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_19 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (5213615460117 / 6250000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140473313647 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨19, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (5213615460117 / 6250000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140473313647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12470_0 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (21019883603471 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (456147643209 / 20000000000000 : ℝ))
      (E := (cell12470 ⟨0, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (21019883603471 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (456147643209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_1 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (10505560594187 / 12500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (45614844061 / 2000000000000 : ℝ))
      (E := (cell12470 ⟨1, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (10505560594187 / 12500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (45614844061 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_2 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (84009460133093 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570186553177 / 25000000000000 : ℝ))
      (E := (cell12470 ⟨2, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (84009460133093 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570186553177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_3 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83974460515939 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (71273443641 / 3125000000000 : ℝ))
      (E := (cell12470 ⟨3, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83974460515939 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (71273443641 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_4 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (20984871466373 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140377110679 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨4, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (20984871466373 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140377110679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_5 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83904536145403 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228075818027 / 10000000000000 : ℝ))
      (E := (cell12470 ⟨5, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83904536145403 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228075818027 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_6 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (16773922263903 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228076219753 / 10000000000000 : ℝ))
      (E := (cell12470 ⟨6, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (16773922263903 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228076219753 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_7 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83834711351861 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (142547885347 / 6250000000000 : ℝ))
      (E := (cell12470 ⟨7, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83834711351861 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (142547885347 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_8 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83799836206663 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140385104101 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨8, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83799836206663 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140385104101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_9 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83764985848329 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280774159293 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨9, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83764985848329 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280774159293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_10 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (5233135015091 / 6250000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280778200229 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨10, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (5233135015091 / 6250000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280778200229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_11 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (41847679675413 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (142548885261 / 6250000000000 : ℝ))
      (E := (cell12470 ⟨11, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (41847679675413 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (142548885261 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_12 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (41830291570701 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228078617411 / 10000000000000 : ℝ))
      (E := (cell12470 ⟨12, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (41830291570701 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228078617411 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_13 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (41812915789167 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570197544667 / 25000000000000 : ℝ))
      (E := (cell12470 ⟨13, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (41812915789167 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570197544667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_14 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (10448888078369 / 12500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280794184259 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨14, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (10448888078369 / 12500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280794184259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_15 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (16711280450553 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280798138911 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨15, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (16711280450553 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280798138911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_16 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (10440215552683 / 12500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280802164793 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨16, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (10440215552683 / 12500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280802164793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_17 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (20871767774729 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140403075639 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨17, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (20871767774729 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140403075639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_18 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83452442251167 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228081016193 / 10000000000000 : ℝ))
      (E := (cell12470 ⟨18, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83452442251167 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228081016193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_19 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83417837844437 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140407071853 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨19, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83417837844437 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140407071853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12471_0 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (42039759360941 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280605811869 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨0, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (42039759360941 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280605811869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_1 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (10505558673839 / 12500000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (28507622611 / 1250000000000 : ℝ))
      (E := (cell12471 ⟨1, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (10505558673839 / 12500000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (28507622611 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_2 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (4200472254953 / 5000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280613771501 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨2, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (4200472254953 / 5000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280613771501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_3 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83974445810191 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (142538610429 / 6250000000000 : ℝ))
      (E := (cell12471 ⟨3, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83974445810191 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (142538610429 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_4 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (16787894297513 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1113584837 / 48828125000 : ℝ))
      (E := (cell12471 ⟨4, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (16787894297513 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1113584837 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_5 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41952261047417 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140312888049 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨5, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41952261047417 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140312888049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_6 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83869597595841 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140314874673 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨6, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83869597595841 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140314874673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_7 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (4191734897731 / 5000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280633732043 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨7, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (4191734897731 / 5000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280633732043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_8 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (16759964627079 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (91225509287 / 4000000000000 : ℝ))
      (E := (cell12471 ⟨8, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (16759964627079 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (91225509287 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_9 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (3350598924103 / 4000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280641757479 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨9, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (3350598924103 / 4000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280641757479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_10 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83730147820757 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (570161439353 / 25000000000000 : ℝ))
      (E := (cell12471 ⟨10, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83730147820757 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (570161439353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_11 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83695347254723 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456129947827 / 20000000000000 : ℝ))
      (E := (cell12471 ⟨11, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83695347254723 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456129947827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_12 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83660571369441 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280653709553 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨12, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83660571369441 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280653709553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_13 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41812910065029 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140328866709 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨13, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41812910065029 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140328866709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_14 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41795546750953 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140330879547 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨14, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41795546750953 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140330879547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_15 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (652784308207 / 781250000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456133146921 / 20000000000000 : ℝ))
      (E := (cell12471 ⟨15, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (652784308207 / 781250000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456133146921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_16 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83521713941519 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280669723959 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨16, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83521713941519 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280669723959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_17 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (20871765235211 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (570168433207 / 25000000000000 : ℝ))
      (E := (cell12471 ⟨17, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (20871765235211 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (570168433207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_18 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (20863108103629 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (228067770843 / 10000000000000 : ℝ))
      (E := (cell12471 ⟨18, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (20863108103629 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (228067770843 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_19 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41708914164379 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280681714111 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨19, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41708914164379 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280681714111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12472_0 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (84079503032399 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (142529587667 / 6250000000000 : ℝ))
      (E := (cell12472 ⟨0, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (84079503032399 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (142529587667 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_1 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (42022227015203 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (570119352433 / 25000000000000 : ℝ))
      (E := (cell12472 ⟨1, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (42022227015203 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (570119352433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_2 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (10501178758433 / 12500000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (228048138319 / 10000000000000 : ℝ))
      (E := (cell12472 ⟨2, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (10501178758433 / 12500000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (228048138319 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_3 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (2099360777671 / 2500000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140242695089 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨3, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (2099360777671 / 2500000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140242695089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_4 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (16787891422399 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (22804893819 / 1000000000000 : ℝ))
      (E := (cell12472 ⟨4, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (16787891422399 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (22804893819 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_5 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (4195225402329 / 5000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (456098673423 / 20000000000000 : ℝ))
      (E := (cell12472 ⟨5, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (4195225402329 / 5000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (456098673423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_6 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (41934791937221 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140248677159 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨6, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (41934791937221 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140248677159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_7 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (16766936911923 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140250675877 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨7, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (16766936911923 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140250675877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_8 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (41899905033161 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280505367409 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨8, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (41899905033161 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280505367409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_9 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (3350598414359 / 4000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140254675509 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨9, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (3350598414359 / 4000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140254675509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_10 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83730135402171 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280513368013 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨10, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83730135402171 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280513368013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_11 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (16739067032139 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140258683787 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨11, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (16739067032139 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140258683787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_12 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83660559599513 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (228052135661 / 10000000000000 : ℝ))
      (E := (cell12472 ⟨12, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83660559599513 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (228052135661 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_13 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (326663315171 / 390625000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140262670889 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨13, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (326663315171 / 390625000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140262670889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_14 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (41795541189407 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (142533083093 / 6250000000000 : ℝ))
      (E := (cell12472 ⟨14, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (41795541189407 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (142533083093 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_15 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83556380650141 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280533325899 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨15, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83556380650141 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280533325899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_16 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83521703463449 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (71266791779 / 3125000000000 : ℝ))
      (E := (cell12472 ⟨16, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83521703463449 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (71266791779 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_17 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (16697410156921 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280541368247 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨17, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (16697410156921 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280541368247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_18 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83452422579659 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (228054536707 / 10000000000000 : ℝ))
      (E := (cell12472 ⟨18, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83452422579659 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (228054536707 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_19 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83417818814833 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280549338513 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨19, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83417818814833 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280549338513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12473_0 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (21019871836359 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140170552013 / 50000000000000 : ℝ))
      (E := (cell12473 ⟨0, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (21019871836359 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140170552013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_1 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (84044438672579 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140172531707 / 50000000000000 : ℝ))
      (E := (cell12473 ⟨1, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (84044438672579 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140172531707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_2 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (84009415038307 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (91213961911 / 4000000000000 : ℝ))
      (E := (cell12473 ⟨2, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (84009415038307 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (91213961911 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_3 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83974416405887 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570088266613 / 25000000000000 : ℝ))
      (E := (cell12473 ⟨3, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83974416405887 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570088266613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_4 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83939442738781 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280357070651 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨4, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83939442738781 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280357070651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_5 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83904494000643 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (18242888553 / 800000000000 : ℝ))
      (E := (cell12473 ⟨5, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83904494000643 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (18242888553 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_6 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (41934785077659 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (18242920563 / 800000000000 : ℝ))
      (E := (cell12473 ⟨6, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (41934785077659 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (18242920563 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_7 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20958667791711 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140184541319 / 50000000000000 : ℝ))
      (E := (cell12473 ⟨7, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20958667791711 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140184541319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_8 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83799796999443 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280373055929 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨8, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83799796999443 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280373055929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_9 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83764947617529 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140188527953 / 50000000000000 : ℝ))
      (E := (cell12473 ⟨9, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83764947617529 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140188527953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_10 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (837301229857 / 1000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280381032027 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨10, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (837301229857 / 1000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280381032027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_11 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83695323068741 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280385049493 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨11, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83695323068741 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280385049493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_12 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (4183027391581 / 5000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280389057211 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨12, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (4183027391581 / 5000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280389057211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_13 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83625797239487 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280393061839 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨13, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83625797239487 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280393061839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_14 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20897767814419 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228039701167 / 10000000000000 : ℝ))
      (E := (cell12473 ⟨14, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20897767814419 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228039701167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_15 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (835563698517 / 1000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228040102907 / 10000000000000 : ℝ))
      (E := (cell12473 ⟨15, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (835563698517 / 1000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228040102907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_16 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20880423246813 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (22804050037 / 1000000000000 : ℝ))
      (E := (cell12473 ⟨16, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20880423246813 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (22804050037 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_17 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83487040630201 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280408999347 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨17, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83487040630201 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280408999347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_18 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83452412746597 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280413021433 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨18, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83452412746597 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280413021433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_19 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83417809302663 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228041701691 / 10000000000000 : ℝ))
      (E := (cell12473 ⟨19, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83417809302663 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228041701691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12474_0 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (84079471660991 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140104400181 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨0, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (84079471660991 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140104400181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_1 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (84044423317229 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280212827741 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨1, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (84044423317229 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280212827741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_2 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (42004700005793 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570054205773 / 25000000000000 : ℝ))
      (E := (cell12474 ⟨2, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (42004700005793 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570054205773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_3 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83974401707329 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280220795691 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨3, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83974401707329 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280220795691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_4 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83939428367923 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (228022481243 / 10000000000000 : ℝ))
      (E := (cell12474 ⟨4, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83939428367923 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (228022481243 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_5 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (4195223997851 / 5000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280228766327 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨5, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (4195223997851 / 5000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280228766327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_6 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (8386955643847 / 10000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140116390831 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨6, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (8386955643847 / 10000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140116390831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_7 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83834657776307 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570059202199 / 25000000000000 : ℝ))
      (E := (cell12474 ⟨7, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83834657776307 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570059202199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_8 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41899891967379 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280240797739 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨8, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41899891967379 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280240797739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_9 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (20941233719559 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280244756151 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨9, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (20941233719559 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280244756151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_10 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41865055285671 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280248749461 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨10, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41865055285671 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280248749461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_11 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (4184765548943 / 5000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (456050556979 / 20000000000000 : ℝ))
      (E := (cell12474 ⟨11, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (4184765548943 / 5000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (456050556979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_12 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83660536065759 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570064188323 / 25000000000000 : ℝ))
      (E := (cell12474 ⟨12, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83660536065759 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570064188323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_13 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83625785797191 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140130388711 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨13, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83625785797191 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140130388711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_14 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83591060138491 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280264747529 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨14, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83591060138491 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280264747529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_15 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (20889089763793 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570067181961 / 25000000000000 : ℝ))
      (E := (cell12474 ⟨15, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (20889089763793 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570067181961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_16 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (2610052578529 / 3125000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140136362139 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨16, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (2610052578529 / 3125000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140136362139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_17 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83487030477631 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280276742501 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨17, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83487030477631 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280276742501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_18 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (40748243611 / 48828125000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280280729731 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨18, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (40748243611 / 48828125000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280280729731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_19 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41708899896123 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280284749307 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨19, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41708899896123 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280284749307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

end BstLean.Part268
