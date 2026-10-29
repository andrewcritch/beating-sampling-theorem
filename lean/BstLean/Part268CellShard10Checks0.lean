import BstLean.Part268CellShard10Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12600_0 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (21019378841539 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263924131887 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨0, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (21019378841539 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263924131887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_1 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (16808501632977 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263928154239 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨1, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (16808501632977 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263928154239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_2 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (42003762971729 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263932126221 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨2, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (42003762971729 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263932126221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_3 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83972568665271 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263936114713 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨3, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83972568665271 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263936114713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_4 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (20984409073479 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1131970064267 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨4, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (20984409073479 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1131970064267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_5 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41951364396587 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (565986029583 / 25000000000000 : ℝ))
      (E := (cell12600 ⟨5, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41951364396587 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (565986029583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_6 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83867846127019 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263948150281 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨6, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83867846127019 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263948150281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_7 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83832988259613 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1131976058251 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨7, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83832988259613 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1131976058251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_8 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41899077577653 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263956140627 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨8, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41899077577653 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263956140627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_9 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (16752669355727 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (90558404567 / 4000000000000 : ℝ))
      (E := (cell12600 ⟨9, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (16752669355727 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (90558404567 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_10 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83728563094323 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (226396410233 / 10000000000000 : ℝ))
      (E := (cell12600 ⟨10, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83728563094323 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (226396410233 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_11 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41846902033639 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263968112059 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨11, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41846902033639 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263968112059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_12 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (20914767415647 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1131986046001 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨12, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (20914767415647 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1131986046001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_13 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83624359845527 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263976106663 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨13, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83624359845527 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263976106663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_14 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83589674581547 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263980104137 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨14, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83589674581547 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263980104137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_15 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41777506918141 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263984090327 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨15, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41777506918141 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263984090327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_16 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83520377575543 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263988129071 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨16, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83520377575543 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263988129071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_17 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41742882882659 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263992109457 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨17, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41742882882659 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2263992109457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_18 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83451178371773 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (226399609481 / 10000000000000 : ℝ))
      (E := (cell12600 ⟨18, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83451178371773 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (226399609481 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_19 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83416615361247 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (113200004503 / 5000000000000 : ℝ))
      (E := (cell12600 ⟨19, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83416615361247 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (113200004503 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12601_0 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (21019374999173 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (282974709333 / 12500000000000 : ℝ))
      (E := (cell12601 ⟨0, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (21019374999173 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (282974709333 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_1 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (21010623279851 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131900828623 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨1, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (21010623279851 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131900828623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_2 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (168015022443 / 200000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131902852943 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨2, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (168015022443 / 200000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131902852943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_3 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83972554266379 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263809656121 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨3, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83972554266379 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263809656121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_4 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41968811108817 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263813690311 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨4, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41968811108817 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263813690311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_5 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41951357519523 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131908850627 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨5, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41951357519523 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131908850627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_6 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (8386783269459 / 10000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (452764339437 / 20000000000000 : ℝ))
      (E := (cell12601 ⟨6, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (8386783269459 / 10000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (452764339437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_7 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (8383297514843 / 10000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (7074455269 / 312500000000 : ℝ))
      (E := (cell12601 ⟨7, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (8383297514843 / 10000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (7074455269 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_8 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (20949535591229 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131914837833 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨8, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (20949535591229 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131914837833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_9 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83763334308587 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263833673411 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨9, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83763334308587 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263833673411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_10 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41864275472083 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263837686537 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨10, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41864275472083 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263837686537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_11 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83693792236561 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (141490103997 / 6250000000000 : ℝ))
      (E := (cell12601 ⟨11, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83693792236561 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (141490103997 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_12 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83659058150863 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131922835193 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨12, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83659058150863 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131922835193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_13 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41812174326173 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131924827101 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨13, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41812174326173 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131924827101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_14 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (2612176990827 / 3125000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263853679681 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨14, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (2612176990827 / 3125000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263853679681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_15 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (1671100065577 / 2000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (452771538929 / 20000000000000 : ℝ))
      (E := (cell12601 ⟨15, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (1671100065577 / 2000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (452771538929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_16 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83520367335317 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263861646579 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨16, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83520367335317 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263861646579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_17 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (16697151168371 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (282983207153 / 12500000000000 : ℝ))
      (E := (cell12601 ⟨17, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (16697151168371 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (282983207153 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_18 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (20862792191157 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263869673603 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨18, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (20862792191157 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263869673603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_19 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83416606069979 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263873642397 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨19, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83416606069979 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263873642397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12602_0 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (8407748462967 / 10000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263671270393 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨0, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (8407748462967 / 10000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263671270393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_1 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (3361699123053 / 4000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263675271093 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨1, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (3361699123053 / 4000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263675271093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_2 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (16801499300381 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (452735856157 / 20000000000000 : ℝ))
      (E := (cell12602 ⟨2, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (16801499300381 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (452735856157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_3 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (83972539869811 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131841625337 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨3, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (83972539869811 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131841625337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_4 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (20984402035909 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131843623701 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨4, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (20984402035909 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131843623701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_5 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41951350643581 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565922819883 / 25000000000000 : ℝ))
      (E := (cell12602 ⟨5, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41951350643581 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565922819883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_6 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (83867819264367 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263695239483 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨6, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (83867819264367 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263695239483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_7 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (83832962039413 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263699251093 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨7, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (83832962039413 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263699251093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_8 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (83798129576653 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (282962908021 / 12500000000000 : ℝ))
      (E := (cell12602 ⟨8, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (83798129576653 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (282962908021 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_9 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (26804262989 / 32000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263707286177 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨9, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (26804262989 / 32000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263707286177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_10 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10466067349507 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131855633151 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨10, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10466067349507 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131855633151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_11 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (20923445101963 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263715269501 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨11, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (20923445101963 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263715269501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_12 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (20914761660277 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263719244407 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨12, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (20914761660277 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263719244407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_13 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10453042182637 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263723255523 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨13, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10453042182637 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263723255523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_14 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10448706604159 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131863625471 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨14, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10448706604159 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131863625471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_15 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (83554992723271 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (282966404571 / 12500000000000 : ℝ))
      (E := (cell12602 ⟨15, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (83554992723271 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (282966404571 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_16 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41760178548453 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263735276233 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨16, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41760178548453 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263735276233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_17 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41742872960083 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565934814757 / 25000000000000 : ℝ))
      (E := (cell12602 ⟨17, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41742872960083 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565934814757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_18 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (4172557957961 / 5000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (141483953017 / 6250000000000 : ℝ))
      (E := (cell12602 ⟨18, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (4172557957961 / 5000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (141483953017 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_19 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (83416596780409 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (452749449779 / 20000000000000 : ℝ))
      (E := (cell12602 ⟨19, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (83416596780409 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (452749449779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12603_0 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (8407746926509 / 10000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565886229769 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨0, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (8407746926509 / 10000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565886229769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_1 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (328290871233 / 390625000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452709776027 / 20000000000000 : ℝ))
      (E := (cell12603 ⟨1, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (328290871233 / 390625000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452709776027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_2 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (84007481784673 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452710581753 / 20000000000000 : ℝ))
      (E := (cell12603 ⟨2, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (84007481784673 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452710581753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_3 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (41986262737783 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263556898373 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨3, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (41986262737783 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263556898373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_4 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83937594071921 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131780457799 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨4, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83937594071921 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131780457799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_5 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (41951343768761 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565891227771 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨5, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (41951343768761 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565891227771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_6 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83867805836347 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131784446531 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨6, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83867805836347 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131784446531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_7 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (1047911861657 / 1250000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (226357286951 / 10000000000000 : ℝ))
      (E := (cell12603 ⟨7, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (1047911861657 / 1250000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (226357286951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_8 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (16759623358103 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (282947113267 / 12500000000000 : ℝ))
      (E := (cell12603 ⟨8, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (16759623358103 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (282947113267 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_9 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (335053237499 / 400000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (113179044723 / 5000000000000 : ℝ))
      (E := (cell12603 ⟨9, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (335053237499 / 400000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (113179044723 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_10 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83728526649993 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263584899661 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨10, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83728526649993 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263584899661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_11 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (2615430268161 / 3125000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (282948608831 / 12500000000000 : ℝ))
      (E := (cell12603 ⟨11, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (2615430268161 / 3125000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (282948608831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_12 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (41829517566661 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263592872147 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨12, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (41829517566661 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263592872147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_13 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (2613260195993 / 3125000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263596910627 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨13, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (2613260195993 / 3125000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263596910627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_14 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (20897410490493 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (45272017521 / 2000000000000 : ℝ))
      (E := (cell12603 ⟨14, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (20897410490493 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (45272017521 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_15 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (10444372771193 / 12500000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263604890553 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨15, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (10444372771193 / 12500000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263604890553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_16 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83520346860307 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263608901687 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨16, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83520346860307 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263608901687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_17 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (20871434000063 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565903228717 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨17, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (20871434000063 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565903228717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_18 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83451149555547 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131808438521 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨18, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83451149555547 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131808438521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_19 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (16683317498507 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131810454779 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨19, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (16683317498507 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131810454779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12604_0 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (10509681737869 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263418562913 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨0, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (10509681737869 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263418562913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_1 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (21010611999343 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (113171130001 / 5000000000000 : ℝ))
      (E := (cell12604 ⟨1, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (21010611999343 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (113171130001 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_2 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (42003733534901 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (226342658983 / 10000000000000 : ℝ))
      (E := (cell12604 ⟨2, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (42003733534901 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (226342658983 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_3 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83972511083643 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263430599219 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨3, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83972511083643 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263430599219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_4 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (10492197500311 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (282929322389 / 12500000000000 : ℝ))
      (E := (cell12604 ⟨4, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (10492197500311 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (282929322389 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_5 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41951336895063 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263438595911 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨5, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41951336895063 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263438595911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_6 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (20966948102633 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131721271019 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨6, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (20966948102633 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131721271019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_7 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (2619779244621 / 3125000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263446541329 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨7, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (2619779244621 / 3125000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263446541329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_8 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41899052003251 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (70732829487 / 3125000000000 : ℝ))
      (E := (cell12604 ⟨8, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41899052003251 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (70732829487 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_9 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83763296910961 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131727278137 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨9, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83763296910961 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131727278137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_10 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83728514505977 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131729293307 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨10, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83728514505977 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131729293307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_11 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (4184687837823 / 5000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263462583511 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨11, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (4184687837823 / 5000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263462583511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_12 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (5228688976719 / 6250000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (226346655361 / 10000000000000 : ℝ))
      (E := (cell12604 ⟨12, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (5228688976719 / 6250000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (226346655361 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_13 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41812157542193 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263470561411 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨13, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41812157542193 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263470561411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_14 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41794815546281 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131737277503 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨14, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41794815546281 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131737277503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_15 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83554971617669 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263478540297 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨15, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83554971617669 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263478540297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_16 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83520336625521 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (565870645279 / 25000000000000 : ℝ))
      (E := (cell12604 ⟨16, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83520336625521 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (565870645279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_17 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (1304464470033 / 1562500000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263486566547 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨17, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (1304464470033 / 1562500000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263486566547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_18 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (8345113995361 / 10000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (282936319989 / 12500000000000 : ℝ))
      (E := (cell12604 ⟨18, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (8345113995361 / 10000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (282936319989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_19 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83416578206359 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131747283069 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨19, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83416578206359 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131747283069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12605_0 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (42038719271627 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263292317507 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨0, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (42038719271627 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263292317507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_1 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (42021216480749 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263296315101 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨1, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (42021216480749 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263296315101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_2 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (84007452357293 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263300266131 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨2, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (84007452357293 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263300266131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_3 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83972496694041 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (141456518459 / 6250000000000 : ℝ))
      (E := (cell12605 ⟨3, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83972496694041 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (141456518459 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_4 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41968782967669 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263308295837 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨4, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41968782967669 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263308295837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_5 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20975665011243 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263312276097 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨5, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20975665011243 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263312276097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_6 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83867778986919 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263316302297 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨6, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83867778986919 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263316302297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_7 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20958230681337 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263320266551 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨7, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20958230681337 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263320266551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_8 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41899045612307 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263324292487 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨8, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41899045612307 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263324292487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_9 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83763284449257 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263328271619 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨9, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83763284449257 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263328271619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_10 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83728502364007 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263332269127 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨10, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83728502364007 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263332269127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_11 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41846872466887 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131668145987 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨11, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41846872466887 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131668145987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_12 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41829506061827 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131670144397 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨12, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41829506061827 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131670144397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_13 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20906075974731 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263344265981 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨13, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20906075974731 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263344265981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_14 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41794810112521 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263348287811 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨14, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41794810112521 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263348287811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_15 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20888740266911 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131676151053 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨15, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20888740266911 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131676151053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_16 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20880081598137 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (282919532043 / 12500000000000 : ℝ))
      (E := (cell12605 ⟨16, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20880081598137 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (282919532043 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_17 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41742858082873 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (282920034033 / 12500000000000 : ℝ))
      (E := (cell12605 ⟨17, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41742858082873 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (282920034033 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_18 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (325980977943 / 390625000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565841074221 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨18, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (325980977943 / 390625000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565841074221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_19 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83416568921879 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263368276883 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨19, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83416568921879 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263368276883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12606_0 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (21019355796499 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (113158303363 / 5000000000000 : ℝ))
      (E := (cell12606 ⟨0, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (21019355796499 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (113158303363 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_1 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (10505302241003 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263170025381 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨1, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (10505302241003 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263170025381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_2 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (10500929705893 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263174053367 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨2, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (10500929705893 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263174053367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_3 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83972482306761 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263178044619 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨3, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83972482306761 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263178044619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_4 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (8393755187047 / 10000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263182065777 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨4, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (8393755187047 / 10000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263182065777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_5 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (4195132315103 / 5000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263186009561 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨5, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (4195132315103 / 5000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263186009561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_6 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (8386776556551 / 10000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452638011591 / 20000000000000 : ℝ))
      (E := (cell12606 ⟨6, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (8386776556551 / 10000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452638011591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_7 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (20958227406247 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (113159702259 / 5000000000000 : ℝ))
      (E := (cell12606 ⟨7, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (20958227406247 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (113159702259 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_8 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (1675961568897 / 2000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (282899754609 / 12500000000000 : ℝ))
      (E := (cell12606 ⟨8, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (1675961568897 / 2000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (282899754609 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_9 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41881635994819 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131601020249 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨9, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41881635994819 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131601020249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_10 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83728490224083 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263206005237 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨10, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83728490224083 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263206005237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_11 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (16738746622619 / 20000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263210054099 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨11, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (16738746622619 / 20000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263210054099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_12 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (20914750155443 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263214019621 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨12, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (20914750155443 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263214019621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_13 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83624292715391 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131609012169 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨13, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83624292715391 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131609012169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_14 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83589609359411 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (113161100817 / 5000000000000 : ℝ))
      (E := (cell12606 ⟨14, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83589609359411 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (113161100817 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_15 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83554950519471 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (90529040061 / 4000000000000 : ℝ))
      (E := (cell12606 ⟨15, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83554950519471 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (90529040061 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_16 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83520316161387 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (90529201749 / 4000000000000 : ℝ))
      (E := (cell12606 ⟨16, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83520316161387 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (90529201749 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_17 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83485706251153 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263234032023 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨17, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83485706251153 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263234032023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_18 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (4172556037747 / 5000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131619014869 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨18, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (4172556037747 / 5000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131619014869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_19 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41708279819547 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452648408359 / 20000000000000 : ℝ))
      (E := (cell12606 ⟨19, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41708279819547 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452648408359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12607_0 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (84077407831177 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263039812171 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨0, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (84077407831177 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263039812171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_1 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (1680848057939 / 2000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263043846507 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨1, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (1680848057939 / 2000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263043846507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_2 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (21001855734839 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263047835841 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨2, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (21001855734839 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263047835841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_3 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83972467921801 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452610369409 / 20000000000000 : ℝ))
      (E := (cell12607 ⟨3, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83972467921801 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452610369409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_4 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83937537807883 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263055831037 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨4, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83937537807883 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263055831037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_5 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (8390263256139 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131529927111 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨5, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (8390263256139 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131529927111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_6 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83867752146303 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (282882976127 / 12500000000000 : ℝ))
      (E := (cell12607 ⟨6, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83867752146303 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (282882976127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_7 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (8383289652679 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263067819251 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨7, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (8383289652679 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263067819251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_8 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83798065667209 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263071834727 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨8, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83798065667209 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263071834727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_9 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (10470407441513 / 12500000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263075804899 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨9, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (10470407441513 / 12500000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263075804899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_10 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (20932119521551 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (8840155449 / 390625000000 : ℝ))
      (E := (cell12607 ⟨10, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (20932119521551 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (8840155449 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_11 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83693721294423 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (141442738239 / 6250000000000 : ℝ))
      (E := (cell12607 ⟨11, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83693721294423 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (141442738239 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_12 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83658989121857 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (565771951043 / 25000000000000 : ℝ))
      (E := (cell12607 ⟨12, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83658989121857 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (565771951043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_13 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83624281533787 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263091836483 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨13, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83624281533787 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263091836483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_14 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (8358959849567 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263095798719 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨14, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (8358959849567 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263095798719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_15 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (20888734993287 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (226309981301 / 10000000000000 : ℝ))
      (E := (cell12607 ⟨15, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (20888734993287 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (226309981301 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_16 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83520305932037 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (565775956727 / 25000000000000 : ℝ))
      (E := (cell12607 ⟨16, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83520305932037 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (565775956727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_17 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83485696338333 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131553922911 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨17, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83485696338333 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131553922911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_18 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83451111158207 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452622363339 / 20000000000000 : ℝ))
      (E := (cell12607 ⟨18, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83451111158207 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452622363339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_19 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (16683310071601 / 20000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263115802629 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨19, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (16683310071601 / 20000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263115802629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12608_0 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (42038696239399 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131456833921 / 50000000000000 : ℝ))
      (E := (cell12608 ⟨0, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (42038696239399 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131456833921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_1 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (3361695514731 / 4000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452583532567 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨1, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (3361695514731 / 4000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452583532567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_2 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (84007408233927 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452584334281 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨2, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (84007408233927 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452584334281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_3 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41986226769581 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (141432852797 / 6250000000000 : ℝ))
      (E := (cell12608 ⟨3, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41986226769581 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (141432852797 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_4 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (10492190468447 / 12500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131464824757 / 50000000000000 : ℝ))
      (E := (cell12608 ⟨4, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (10492190468447 / 12500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131464824757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_5 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83902618822961 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282866704541 / 12500000000000 : ℝ))
      (E := (cell12608 ⟨5, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83902618822961 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282866704541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_6 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83867738729297 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131468835681 / 50000000000000 : ℝ))
      (E := (cell12608 ⟨6, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83867738729297 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131468835681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_7 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (16766576686151 / 20000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262941646729 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨7, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (16766576686151 / 20000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262941646729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_8 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (20949513222923 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131472843027 / 50000000000000 : ℝ))
      (E := (cell12608 ⟨8, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (20949513222923 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131472843027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_9 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83763247076653 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (141434355053 / 6250000000000 : ℝ))
      (E := (cell12608 ⟨9, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83763247076653 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (141434355053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_10 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (8372846595037 / 10000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (9051814553 / 400000000000 : ℝ))
      (E := (cell12608 ⟨10, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (8372846595037 / 10000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (9051814553 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_11 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (20923427369439 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282869710159 / 12500000000000 : ℝ))
      (E := (cell12608 ⟨11, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (20923427369439 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282869710159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_12 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83658977623909 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (141435102653 / 6250000000000 : ℝ))
      (E := (cell12608 ⟨12, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83658977623909 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (141435102653 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_13 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (8362427035411 / 10000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282870705539 / 12500000000000 : ℝ))
      (E := (cell12608 ⟨13, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (8362427035411 / 10000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282870705539 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_14 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41794793816909 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (45259392699 / 2000000000000 : ℝ))
      (E := (cell12608 ⟨14, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41794793816909 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (45259392699 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_15 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (3342197177147 / 4000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565743419603 / 25000000000000 : ℝ))
      (E := (cell12608 ⟨15, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (3342197177147 / 4000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565743419603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_16 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41760147852249 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262977664071 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨16, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41760147852249 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262977664071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_17 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (16697137285457 / 20000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452596331093 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨17, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (16697137285457 / 20000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452596331093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_18 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83451101563207 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262985657759 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨18, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83451101563207 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262985657759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_19 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83416541078611 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262989675877 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨19, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83416541078611 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262989675877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12609_0 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (10509672141107 / 12500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565696879669 / 25000000000000 : ℝ))
      (E := (cell12609 ⟨0, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (10509672141107 / 12500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565696879669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_1 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (42021186420999 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (226279153219 / 10000000000000 : ℝ))
      (E := (cell12609 ⟨1, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (42021186420999 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (226279153219 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_2 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (42003696765429 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262795560059 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨2, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (42003696765429 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262795560059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_3 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83972439158841 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262799553487 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨3, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83972439158841 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262799553487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_4 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83937509689549 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262803521211 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨4, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83937509689549 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262803521211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_5 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (20975651271693 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452561505927 / 20000000000000 : ℝ))
      (E := (cell12609 ⟨5, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (20975651271693 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452561505927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_6 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83867725314493 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131405764557 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨6, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83867725314493 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131405764557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_7 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83832870336881 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (113140776381 / 5000000000000 : ℝ))
      (E := (cell12609 ⟨7, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83832870336881 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (113140776381 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_8 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83798040118297 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565704883217 / 25000000000000 : ℝ))
      (E := (cell12609 ⟨8, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83798040118297 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565704883217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_9 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41881617311643 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131411776161 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨9, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41881617311643 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131411776161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_10 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (4186422690829 / 5000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262827535159 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨10, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (4186422690829 / 5000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262827535159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_11 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41846848831547 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131415773163 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨11, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41846848831547 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131415773163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_12 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83658966127927 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131417767227 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨12, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83658966127927 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131417767227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_13 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (2090606479409 / 2500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262839505933 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨13, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (2090606479409 / 2500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262839505933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_14 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41794788386927 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262843525037 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨14, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41794788386927 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262843525037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_15 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83554918886051 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (113142376979 / 5000000000000 : ℝ))
      (E := (cell12609 ⟨15, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83554918886051 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (113142376979 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_16 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (8352028547877 / 10000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (28285643713 / 1250000000000 : ℝ))
      (E := (cell12609 ⟨16, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (8352028547877 / 10000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (28285643713 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_17 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83485676518009 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262855519153 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨17, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83485676518009 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262855519153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_18 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (4172554598497 / 5000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (226285955293 / 10000000000000 : ℝ))
      (E := (cell12609 ⟨18, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (4172554598497 / 5000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (226285955293 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_19 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (5213533237557 / 6250000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (45257270901 / 2000000000000 : ℝ))
      (E := (cell12609 ⟨19, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (5213533237557 / 6250000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (45257270901 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12610_0 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (84077361781353 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262661480273 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨0, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (84077361781353 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262661480273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_1 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (2101058945453 / 2500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (226266545457 / 10000000000000 : ℝ))
      (E := (cell12610 ⟨1, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (2101058945453 / 2500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (226266545457 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_2 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (42003689415073 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131334721979 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨2, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (42003689415073 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131334721979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_3 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (2099310619521 / 2500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (70708545547 / 3125000000000 : ℝ))
      (E := (cell12610 ⟨3, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (2099310619521 / 2500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (70708545547 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_4 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41968747816901 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131338723063 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨4, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41968747816901 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131338723063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_5 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (10487823919103 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (17677199033 / 781250000000 : ℝ))
      (E := (cell12610 ⟨5, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (10487823919103 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (17677199033 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_6 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83867711901889 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565671360053 / 25000000000000 : ℝ))
      (E := (cell12610 ⟨6, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83867711901889 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565671360053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_7 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83832857245169 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262689461919 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨7, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83832857245169 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262689461919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_8 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (5237376709189 / 6250000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452538686631 / 20000000000000 : ℝ))
      (E := (cell12610 ⟨8, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (5237376709189 / 6250000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452538686631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_9 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41881611086001 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131348709661 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨9, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41881611086001 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131348709661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_10 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41864220842417 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (141418839227 / 6250000000000 : ℝ))
      (E := (cell12610 ⟨10, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41864220842417 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (141418839227 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_11 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83693685850437 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452541093009 / 20000000000000 : ℝ))
      (E := (cell12610 ⟨11, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83693685850437 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452541093009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_12 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (8365895463391 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131354711053 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨12, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (8365895463391 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131354711053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_13 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (10453031000067 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131356710673 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨13, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (10453031000067 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131356710673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_14 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41794782957889 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131358734489 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨14, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41794782957889 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131358734489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_15 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (20888727086319 / 25000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131360727333 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨15, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (20888727086319 / 25000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131360727333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_16 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (20880068813713 / 25000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131362721083 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨16, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (20880068813713 / 25000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131362721083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_17 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (10435708326313 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452545887377 / 20000000000000 : ℝ))
      (E := (cell12610 ⟨17, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (10435708326313 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452545887377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_18 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41725541189203 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131366721993 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨18, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41725541189203 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131366721993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_19 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83416522524907 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262737410147 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨19, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83416522524907 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262737410147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12611_0 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (84077346436287 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131267718517 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨0, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (84077346436287 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131267718517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_1 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (84042342796639 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (113126971499 / 5000000000000 : ℝ))
      (E := (cell12611 ⟨1, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (84042342796639 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (113126971499 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_2 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (84007364131793 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (565635845237 / 25000000000000 : ℝ))
      (E := (cell12611 ⟨2, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (84007364131793 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (565635845237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_3 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83972410405157 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131273707339 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨3, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83972410405157 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131273707339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_4 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83937481580333 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131275712131 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨4, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83937481580333 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131275712131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_5 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41951288810557 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262555418181 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨5, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41951288810557 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262555418181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_6 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (16773539698297 / 20000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262559404659 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨6, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (16773539698297 / 20000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262559404659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_7 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83832844155617 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131281695833 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨7, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83832844155617 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131281695833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_8 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83798014577873 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262567386917 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨8, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83798014577873 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262567386917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_9 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (209408024307 / 250000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262571397873 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨9, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (209408024307 / 250000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262571397873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_10 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83728429555131 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262575373709 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨10, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83728429555131 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262575373709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_11 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83693674039783 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (565644844843 / 25000000000000 : ℝ))
      (E := (cell12611 ⟨11, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83693674039783 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (565644844843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_12 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83658943141859 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262583421569 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨12, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83658943141859 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262583421569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_13 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83624236826639 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262587390551 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨13, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83624236826639 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262587390551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_14 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83589555059589 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262591408647 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨14, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83589555059589 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262591408647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_15 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (1671097956127 / 2000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262595365519 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨15, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (1671097956127 / 2000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262595365519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_16 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (10440033129093 / 12500000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262599383099 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨16, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (10440033129093 / 12500000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262599383099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_17 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83485656704771 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131301704331 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨17, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83485656704771 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131301704331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_18 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (16690214557721 / 20000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262607389151 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨18, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (16690214557721 / 20000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262607389151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_19 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (16683302650119 / 20000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262611387663 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨19, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (16683302650119 / 20000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262611387663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12612_0 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (84077331093657 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262409388961 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨0, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (84077331093657 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262409388961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_1 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (16808465555511 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262413400597 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨1, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (16808465555511 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262413400597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_2 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (84007349435797 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262417428881 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨2, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (84007349435797 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262417428881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_3 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (5248274751987 / 6250000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262421425011 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨3, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (5248274751987 / 6250000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262421425011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_4 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83937467529143 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131212698863 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨4, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83937467529143 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131212698863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_5 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (20975640972911 / 25000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262429413423 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨5, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (20975640972911 / 25000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262429413423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_6 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83867685083281 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452486684491 / 20000000000000 : ℝ))
      (E := (cell12612 ⟨6, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83867685083281 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452486684491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_7 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41916415534113 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262437374827 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨7, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41916415534113 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262437374827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_8 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83798001810843 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131220697079 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨8, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83798001810843 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131220697079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_9 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (523519982973 / 625000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131222685977 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨9, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (523519982973 / 625000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131222685977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_10 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (8372841742747 / 10000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262449373391 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨10, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (8372841742747 / 10000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262449373391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_11 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41846831115567 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (90498136217 / 4000000000000 : ℝ))
      (E := (cell12612 ⟨11, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41846831115567 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (90498136217 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_12 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (20914732912943 / 25000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262457416683 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨12, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (20914732912943 / 25000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262457416683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_13 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (20906056413667 / 25000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (141403838347 / 6250000000000 : ℝ))
      (E := (cell12612 ⟨13, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (20906056413667 / 25000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (141403838347 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_14 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83589544205287 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (90498616087 / 4000000000000 : ℝ))
      (E := (cell12612 ⟨14, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83589544205287 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (90498616087 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_15 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (10444360908659 / 12500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131234694223 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨15, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (10444360908659 / 12500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131234694223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_16 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (16704050962489 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262473378017 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨16, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (16704050962489 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262473378017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_17 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (10435705850101 / 12500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262477376289 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨17, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (10435705850101 / 12500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262477376289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_18 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (16690212640107 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (565620347107 / 25000000000000 : ℝ))
      (E := (cell12612 ⟨18, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (16690212640107 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (565620347107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_19 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83416503977977 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262485361107 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨19, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83416503977977 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262485361107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12613_0 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (84077315753463 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (282785431457 / 12500000000000 : ℝ))
      (E := (cell12613 ⟨0, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (84077315753463 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (282785431457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_1 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (84042312760867 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452457484849 / 20000000000000 : ℝ))
      (E := (cell12613 ⟨1, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (84042312760867 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452457484849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_2 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (42003667371079 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131145707107 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨2, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (42003667371079 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131145707107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_3 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (10496547707593 / 12500000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262295430633 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨3, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (10496547707593 / 12500000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262295430633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_4 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83937453480231 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262299424413 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨4, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83937453480231 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262299424413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_5 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (20975637541103 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452460680807 / 20000000000000 : ℝ))
      (E := (cell12613 ⟨5, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (20975637541103 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452460680807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_6 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (20966917919319 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131153717831 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨6, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (20966917919319 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131153717831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_7 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (16766563596599 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262311411403 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨7, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (16766563596599 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262311411403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_8 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83797989045933 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262315454877 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨8, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83797989045933 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262315454877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_9 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83763184830641 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262319399577 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨9, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83763184830641 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262319399577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_10 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83728405301853 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131161713339 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨10, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83728405301853 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131161713339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_11 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (10461706303061 / 12500000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262327427089 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨11, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (10461706303061 / 12500000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262327427089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_12 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83658920163649 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262331407447 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨12, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83658920163649 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262331407447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_13 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (41812107242311 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565583858061 / 25000000000000 : ℝ))
      (E := (cell12613 ⟨13, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (41812107242311 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565583858061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_14 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83589533352871 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131169724781 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨14, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83589533352871 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131169724781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_15 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83554876734041 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (282792925893 / 12500000000000 : ℝ))
      (E := (cell12613 ⟨15, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83554876734041 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (282792925893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_16 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (16704048918791 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262347426921 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨16, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (16704048918791 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262347426921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_17 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (16697127379723 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452470279593 / 20000000000000 : ℝ))
      (E := (cell12613 ⟨17, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (16697127379723 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452470279593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_18 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83451053614197 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262355441817 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨18, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83451053614197 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262355441817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_19 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (20854123676763 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565589861743 / 25000000000000 : ℝ))
      (E := (cell12613 ⟨19, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (20854123676763 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565589861743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12614_0 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (16815460083141 / 20000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262157509519 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨0, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (16815460083141 / 20000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262157509519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_1 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (5252643609161 / 6250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (90486460037 / 4000000000000 : ℝ))
      (E := (cell12614 ⟨1, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (5252643609161 / 6250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (90486460037 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_2 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (42003660025437 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262165510493 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨2, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (42003660025437 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262165510493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_3 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83972367292013 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (452433897883 / 20000000000000 : ℝ))
      (E := (cell12614 ⟨3, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83972367292013 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (452433897883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_4 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (16787487886719 / 20000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (90486940173 / 4000000000000 : ℝ))
      (E := (cell12614 ⟨4, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (16787487886719 / 20000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (90486940173 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_5 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (41951268219709 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131088752927 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨5, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (41951268219709 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131088752927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_6 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83867658273469 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262181502221 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨6, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83867658273469 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262181502221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_7 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83832804899923 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131092750697 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨7, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83832804899923 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131092750697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_8 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (10474747035393 / 12500000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262189511087 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨8, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (10474747035393 / 12500000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262189511087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_9 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83763172387683 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (282774185093 / 12500000000000 : ℝ))
      (E := (cell12614 ⟨9, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83763172387683 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (282774185093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_10 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20932098294569 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131098737769 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨10, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20932098294569 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131098737769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_11 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20923409654961 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (282775187803 / 12500000000000 : ℝ))
      (E := (cell12614 ⟨11, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20923409654961 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (282775187803 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_12 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83658908677491 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131102755013 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨12, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83658908677491 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131102755013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_13 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83624203316501 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (565552376183 / 25000000000000 : ℝ))
      (E := (cell12614 ⟨13, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83624203316501 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (565552376183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_14 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83589522502341 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262213492681 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨14, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83589522502341 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262213492681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_15 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83554866200657 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131108739883 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨15, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83554866200657 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131108739883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_16 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83520234377273 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (452444294327 / 20000000000000 : ℝ))
      (E := (cell12614 ⟨16, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83520234377273 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (452444294327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_17 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (5217851687387 / 6250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262225473691 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨17, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (5217851687387 / 6250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262225473691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_18 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83451044029589 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (282778686387 / 12500000000000 : ℝ))
      (E := (cell12614 ⟨18, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83451044029589 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (282778686387 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_19 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83416485437819 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262233470521 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨19, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83416485437819 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262233470521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12615_0 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (84077285080381 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (8836061017 / 390625000000 : ℝ))
      (E := (cell12615 ⟨0, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (84077285080381 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (8836061017 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_1 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (84042282734679 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (28275445383 / 1250000000000 : ℝ))
      (E := (cell12615 ⟨1, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (84042282734679 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (28275445383 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_2 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (84007305361947 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (113101980101 / 5000000000000 : ℝ))
      (E := (cell12615 ⟨2, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (84007305361947 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (113101980101 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_3 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41986176462799 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262043601359 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨3, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41986176462799 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262043601359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_4 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83937425389237 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262047637463 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨4, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83937425389237 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262047637463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_5 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41951261358331 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262051603043 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨5, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41951261358331 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262051603043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_6 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (4193382243593 / 5000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262055622133 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨6, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (4193382243593 / 5000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262055622133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_7 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83832791819009 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262059586839 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨7, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83832791819009 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262059586839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_8 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41898981761237 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131031810389 / 50000000000000 : ℝ))
      (E := (cell12615 ⟨8, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41898981761237 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131031810389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_9 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16752631989361 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (452413523091 / 20000000000000 : ℝ))
      (E := (cell12615 ⟨9, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16752631989361 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (452413523091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_10 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83728381056741 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (56551790901 / 2500000000000 : ℝ))
      (E := (cell12615 ⟨10, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83728381056741 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (56551790901 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_11 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83693626817203 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (226207563143 / 10000000000000 : ℝ))
      (E := (cell12615 ⟨11, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83693626817203 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (226207563143 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_12 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16731779438659 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131039804129 / 50000000000000 : ℝ))
      (E := (cell12615 ⟨12, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16731779438659 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131039804129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_13 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (2613256004697 / 3125000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262083631019 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨13, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (2613256004697 / 3125000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262083631019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_14 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83589511653697 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (113104379483 / 5000000000000 : ℝ))
      (E := (cell12615 ⟨14, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83589511653697 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (113104379483 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_15 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (130554461983 / 156250000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (282761450789 / 12500000000000 : ℝ))
      (E := (cell12615 ⟨15, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (130554461983 / 156250000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (282761450789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_16 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (104400280203 / 125000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262095628513 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨16, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (104400280203 / 125000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262095628513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_17 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41742808549769 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565524900867 / 25000000000000 : ℝ))
      (E := (cell12615 ⟨17, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41742808549769 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565524900867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_18 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83451034446713 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (282762949311 / 12500000000000 : ℝ))
      (E := (cell12615 ⟨18, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83451034446713 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (282762949311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_19 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83416476170279 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565526901623 / 25000000000000 : ℝ))
      (E := (cell12615 ⟨19, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83416476170279 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565526901623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12616_0 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (21019317436873 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565476446039 / 25000000000000 : ℝ))
      (E := (cell12616 ⟨0, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (21019317436873 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565476446039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_1 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (84042267725177 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452381951113 / 20000000000000 : ℝ))
      (E := (cell12616 ⟨1, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (84042267725177 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452381951113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_2 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (672058325403 / 800000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261913746647 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨2, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (672058325403 / 800000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261913746647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_3 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41986169280749 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261917766467 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨3, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41986169280749 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261917766467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_4 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41968705673577 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1130960882967 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨4, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41968705673577 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1130960882967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_5 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41951254498071 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565481438381 / 25000000000000 : ℝ))
      (E := (cell12616 ⟨5, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41951254498071 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565481438381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_6 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83867631472449 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (11309648977 / 500000000000 : ℝ))
      (E := (cell12616 ⟨6, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83867631472449 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (11309648977 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_7 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41916389370127 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1130966891833 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨7, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41916389370127 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1130966891833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_8 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41898975381961 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (141371111497 / 6250000000000 : ℝ))
      (E := (cell12616 ⟨8, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41898975381961 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (141371111497 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_9 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83763147508007 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261941745699 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨9, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83763147508007 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261941745699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_10 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83728368937247 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (7068580419 / 312500000000 : ℝ))
      (E := (cell12616 ⟨10, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83728368937247 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (7068580419 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_11 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83693615016563 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261949756049 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨11, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83693615016563 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261949756049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_12 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41829442855531 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261953760227 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨12, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41829442855531 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261953760227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_13 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83624180986031 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1130978876499 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨13, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83624180986031 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1130978876499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_14 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83589500806937 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261961740503 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨14, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83589500806937 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261961740503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_15 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83554845139429 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (70686430837 / 3125000000000 : ℝ))
      (E := (cell12616 ⟨15, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83554845139429 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (70686430837 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_16 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83520213949333 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452393956241 / 20000000000000 : ℝ))
      (E := (cell12616 ⟨16, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83520213949333 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452393956241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_17 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (20871401800663 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261973787297 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨17, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (20871401800663 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261973787297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_18 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41725512432783 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261977751997 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨18, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41725512432783 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261977751997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_19 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83416466904429 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565495434599 / 25000000000000 : ℝ))
      (E := (cell12616 ⟨19, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83416466904429 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565495434599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12617_0 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (21019313604259 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261779943133 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨0, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (21019313604259 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261779943133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_1 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (84042252718069 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130891995677 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨1, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (84042252718069 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130891995677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_2 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (84007275991157 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (282723493047 / 12500000000000 : ℝ))
      (E := (cell12617 ⟨2, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (84007275991157 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (282723493047 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_3 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41986162099857 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (113089599237 / 5000000000000 : ℝ))
      (E := (cell12617 ⟨3, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41986162099857 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (113089599237 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_4 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (20984349326837 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261795947633 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨4, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (20984349326837 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261795947633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_5 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41951247638929 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130899978649 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨5, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41951247638929 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130899978649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_6 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41933809037617 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261803964083 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨6, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41933809037617 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261803964083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_7 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (10479095707957 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (45236159519 / 2000000000000 : ℝ))
      (E := (cell12617 ⟨7, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (10479095707957 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (45236159519 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_8 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (8379793800749 / 10000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (113090597131 / 5000000000000 : ℝ))
      (E := (cell12617 ⟨8, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (8379793800749 / 10000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (113090597131 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_9 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83763135071289 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261815929491 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨9, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83763135071289 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261815929491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_10 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83728356819793 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (282727492971 / 12500000000000 : ℝ))
      (E := (cell12617 ⟨10, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83728356819793 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (282727492971 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_11 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (3347744128717 / 4000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261823934343 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨11, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (3347744128717 / 4000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261823934343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_12 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83658874230791 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130913982967 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨12, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83658874230791 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130913982967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_13 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83624169823681 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261831928781 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨13, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83624169823681 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261831928781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_14 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41794744981031 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261835945211 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨14, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41794744981031 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261835945211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_15 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (652772145403 / 781250000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261839963031 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨15, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (652772145403 / 781250000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261839963031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_16 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41760101869037 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261843929711 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨16, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41760101869037 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261843929711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_17 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (16697119461507 / 20000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261847966981 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨17, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (16697119461507 / 20000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261847966981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_18 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83451015286149 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261851963623 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨18, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83451015286149 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261851963623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_19 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83416457640271 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1767074941 / 78125000000 : ℝ))
      (E := (cell12617 ⟨19, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83416457640271 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1767074941 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12618_0 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (42038619544507 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452330842577 / 20000000000000 : ℝ))
      (E := (cell12618 ⟨0, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (42038619544507 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452330842577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_1 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (16808447542671 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452331644471 / 20000000000000 : ℝ))
      (E := (cell12618 ⟨1, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (16808447542671 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452331644471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_2 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (84007261309293 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (282707774401 / 12500000000000 : ℝ))
      (E := (cell12618 ⟨2, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (84007261309293 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (282707774401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_3 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (20993077460061 / 25000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565416549577 / 25000000000000 : ℝ))
      (E := (cell12618 ⟨3, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (20993077460061 / 25000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565416549577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_4 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (10492172908727 / 12500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261670182563 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨4, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (10492172908727 / 12500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261670182563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_5 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (8390248156181 / 10000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130837107183 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨5, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (8390248156181 / 10000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130837107183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_6 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (10483450585027 / 12500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261678186123 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨6, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (10483450585027 / 12500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261678186123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_7 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (16766550517843 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261682163689 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨7, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (16766550517843 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261682163689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_8 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (3351917010127 / 4000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130843106381 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨8, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (3351917010127 / 4000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130843106381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_9 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83763122636649 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (141355635427 / 6250000000000 : ℝ))
      (E := (cell12618 ⟨9, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83763122636649 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (141355635427 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_10 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83728344704379 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261694207067 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨10, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83728344704379 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261694207067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_11 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83693591421287 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261698166313 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨11, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83693591421287 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261698166313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_12 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83658862752483 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (8834774091 / 390625000000 : ℝ))
      (E := (cell12618 ⟨12, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83658862752483 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (8834774091 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_13 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41812079331627 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565426539591 / 25000000000000 : ℝ))
      (E := (cell12618 ⟨13, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41812079331627 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565426539591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_14 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83589479119071 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (282713775473 / 12500000000000 : ℝ))
      (E := (cell12618 ⟨14, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83589479119071 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (282713775473 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_15 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (5222176505349 / 6250000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261714193207 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨15, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (5222176505349 / 6250000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261714193207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_16 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83520193528621 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452343638077 / 20000000000000 : ℝ))
      (E := (cell12618 ⟨16, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83520193528621 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452343638077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_17 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41742793707093 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (28271527509 / 1250000000000 : ℝ))
      (E := (cell12618 ⟨17, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41742793707093 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (28271527509 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_18 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41725502854231 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130863085571 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨18, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41725502854231 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130863085571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_19 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (20854112094451 / 25000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452346032949 / 20000000000000 : ℝ))
      (E := (cell12618 ⟨19, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (20854112094451 / 25000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452346032949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12619_0 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (2627413242607 / 3125000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565382119453 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨0, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (2627413242607 / 3125000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565382119453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_1 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (84042222711033 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565383112143 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨1, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (84042222711033 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565383112143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_2 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (42003623314891 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452307288259 / 20000000000000 : ℝ))
      (E := (cell12619 ⟨2, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (42003623314891 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452307288259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_3 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83972295483087 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565385116261 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨3, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83972295483087 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565385116261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_4 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83937369234559 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565386117681 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨4, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83937369234559 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565386117681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_5 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83902467847997 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565387116703 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨5, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83902467847997 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565387116703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_6 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (41933795643697 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130776230761 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨6, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (41933795643697 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130776230761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_7 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83832739516931 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261556462817 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨7, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83832739516931 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261556462817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_8 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83797912500977 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565390119601 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨8, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83797912500977 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565390119601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_9 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (10470388775511 / 12500000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261564457723 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨9, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (10470388775511 / 12500000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261564457723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_10 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83728332591003 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130784232973 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨10, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83728332591003 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130784232973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_11 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (1673871592533 / 2000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (56539311299 / 2500000000000 : ℝ))
      (E := (cell12619 ⟨11, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (1673871592533 / 2000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (56539311299 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_12 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (16731770255227 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261576480483 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨12, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (16731770255227 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261576480483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_13 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83624147504749 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261580441753 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨13, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83624147504749 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261580441753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_14 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (20897367069491 / 25000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130792229047 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨14, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (20897367069491 / 25000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130792229047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_15 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83554813561429 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130794238657 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨15, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83554813561429 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130794238657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_16 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (41760091660487 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261592446877 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨16, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (41760091660487 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261592446877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_17 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (16697115504521 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130798215157 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨17, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (16697115504521 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130798215157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_18 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83450996132503 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130800216391 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨18, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83450996132503 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130800216391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_19 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83416439117027 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (282700557399 / 12500000000000 : ℝ))
      (E := (cell12619 ⟨19, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83416439117027 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (282700557399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12620_0 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (42038604220133 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452280559143 / 20000000000000 : ℝ))
      (E := (cell12620 ⟨0, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (42038604220133 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452280559143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_1 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (656579747743 / 781250000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130703392827 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨1, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (656579747743 / 781250000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130703392827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_2 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (672057855621 / 800000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452282159667 / 20000000000000 : ℝ))
      (E := (cell12620 ⟨2, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (672057855621 / 800000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452282159667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_3 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (16794456225649 / 20000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565353696237 / 25000000000000 : ℝ))
      (E := (cell12620 ⟨3, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (16794456225649 / 20000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565353696237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_4 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (3357494208063 / 4000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (141338672139 / 6250000000000 : ℝ))
      (E := (cell12620 ⟨4, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (3357494208063 / 4000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (141338672139 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_5 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41951227068209 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130711386277 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨5, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41951227068209 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130711386277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_6 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83867577896767 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261426790281 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨6, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83867577896767 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261426790281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_7 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83832726446803 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130715378701 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨7, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83832726446803 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130715378701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_8 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83797899750897 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261434797531 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨8, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83797899750897 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261434797531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_9 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (20940774443401 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261438744153 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨9, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (20940774443401 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261438744153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_10 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83728320479667 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261442778437 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨10, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83728320479667 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261442778437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_11 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (20923391958503 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452289358257 / 20000000000000 : ℝ))
      (E := (cell12620 ⟨11, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (20923391958503 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452289358257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_12 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (20914709950437 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261450789327 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨12, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (20914709950437 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261450789327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_13 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83624136348167 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (35335230921 / 1562500000000 : ℝ))
      (E := (cell12620 ⟨13, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83624136348167 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (35335230921 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_14 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (4179472871937 / 5000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (35335293223 / 1562500000000 : ℝ))
      (E := (cell12620 ⟨14, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (4179472871937 / 5000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (35335293223 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_15 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83554803039119 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261462757197 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨15, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83554803039119 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261462757197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_16 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83520173115133 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261466757363 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨16, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83520173115133 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261466757363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_17 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (8348556763279 / 10000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261470772167 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨17, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (8348556763279 / 10000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261470772167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_18 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83450986558273 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261474748541 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨18, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83450986558273 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261474748541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_19 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (4170821492897 / 5000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (282684843697 / 12500000000000 : ℝ))
      (E := (cell12620 ⟨19, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (4170821492897 / 5000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (282684843697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12621_0 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (84077193119539 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (452255421759 / 20000000000000 : ℝ))
      (E := (cell12621 ⟨0, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (84077193119539 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (452255421759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_1 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (84042192713567 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261281117953 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨1, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (84042192713567 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261281117953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_2 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (84007217277819 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130642575317 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨2, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (84007217277819 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130642575317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_3 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (16794453355143 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (45225782003 / 2000000000000 : ℝ))
      (E := (cell12621 ⟨3, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (16794453355143 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (45225782003 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_4 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (16787468234173 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565323287213 / 25000000000000 : ℝ))
      (E := (cell12621 ⟨4, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (16787468234173 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565323287213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_5 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41951220213537 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261297131593 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨5, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41951220213537 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261297131593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_6 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (16773512901667 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261301114459 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨6, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (16773512901667 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261301114459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_7 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (83832713378831 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261305105413 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨7, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (83832713378831 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261305105413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_8 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (83797887002933 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130654556079 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨8, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (83797887002933 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130654556079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_9 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41881542672599 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261313142147 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨9, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41881542672599 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261313142147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_10 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (83728308370369 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (452263428909 / 20000000000000 : ℝ))
      (E := (cell12621 ⟨10, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (83728308370369 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (452263428909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_11 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41846778021687 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261321126229 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨11, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41846778021687 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261321126229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_12 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41829414164661 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261325093831 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨12, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41829414164661 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261325093831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_13 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41812062596753 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565332277959 / 25000000000000 : ℝ))
      (E := (cell12621 ⟨13, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41812062596753 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565332277959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_14 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41794723300699 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261333128319 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨14, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41794723300699 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261333128319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_15 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (20888698129663 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261337091013 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨15, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (20888698129663 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261337091013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_16 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (83520162911097 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565335280461 / 25000000000000 : ℝ))
      (E := (cell12621 ⟨16, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (83520162911097 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565335280461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_17 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41742778872371 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261345109877 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨17, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41742778872371 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261345109877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_18 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (83450976985771 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130674559211 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨18, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (83450976985771 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130674559211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_19 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41708210300271 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2208352631 / 97656250000 : ℝ))
      (E := (cell12621 ⟨19, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41708210300271 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2208352631 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12622_0 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (84077177801243 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130575766329 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨0, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (84077177801243 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130575766329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_1 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (84042177718421 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261155503297 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨1, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (84042177718421 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261155503297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_2 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (16801440521073 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (141322468637 / 6250000000000 : ℝ))
      (E := (cell12622 ⟨2, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (16801440521073 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (141322468637 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_3 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83972252425497 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130581763199 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨3, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83972252425497 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130581763199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_4 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20984331785607 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130583769411 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨4, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20984331785607 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130583769411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_5 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83902426719963 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261171486013 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨5, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83902426719963 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261171486013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_6 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83867551122097 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130587746001 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨6, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83867551122097 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130587746001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_7 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41916350156507 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261179506851 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨7, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41916350156507 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261179506851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_8 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (16759574851417 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565295870069 / 25000000000000 : ℝ))
      (E := (cell12622 ⟨8, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (16759574851417 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565295870069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_9 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20940768229717 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261187477671 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨9, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20940768229717 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261187477671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_10 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83728296263109 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130595753117 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨10, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83728296263109 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130595753117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_11 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41846772127367 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (282649439357 / 12500000000000 : ℝ))
      (E := (cell12622 ⟨11, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41846772127367 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (282649439357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_12 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (16731763371771 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261199510163 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨12, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (16731763371771 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261199510163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_13 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41812057020383 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (282650437317 / 12500000000000 : ℝ))
      (E := (cell12622 ⟨13, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41812057020383 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (282650437317 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_14 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83589435765939 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565301871527 / 25000000000000 : ℝ))
      (E := (cell12622 ⟨14, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83589435765939 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565301871527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_15 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20888695500007 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452242295753 / 20000000000000 : ℝ))
      (E := (cell12622 ⟨15, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20888695500007 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452242295753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_16 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41760076354433 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452243096429 / 20000000000000 : ℝ))
      (E := (cell12622 ⟨16, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41760076354433 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452243096429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_17 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (4174277392923 / 5000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261219501649 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨17, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (4174277392923 / 5000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261219501649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_18 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20862741853749 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565305871051 / 25000000000000 : ℝ))
      (E := (cell12622 ⟨18, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20862741853749 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565305871051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_19 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41708205672417 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130613746449 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨19, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41708205672417 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130613746449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12623_0 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (42038581242689 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261025951699 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨0, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (42038581242689 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261025951699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_1 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (16808432545133 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130514970843 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨1, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (16808432545133 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130514970843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_2 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (84007187935263 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261033956707 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨2, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (84007187935263 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261033956707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_3 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83972238077591 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130518973973 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨3, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83972238077591 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130518973973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_4 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83937313116263 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261041924131 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨4, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83937313116263 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261041924131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_5 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41951206507543 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565261487913 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨5, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41951206507543 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565261487913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_6 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83867537738053 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565262480727 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨6, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83867537738053 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565262480727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_7 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83832687249351 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261053961717 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨7, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83832687249351 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261053961717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_8 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (10474732689169 / 12500000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (18088463679 / 800000000000 : ℝ))
      (E := (cell12623 ⟨8, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (10474732689169 / 12500000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (18088463679 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_9 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (16752612098923 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130530962381 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨9, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (16752612098923 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130530962381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_10 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (16745656831577 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130532960771 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨10, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (16745656831577 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130532960771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_11 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (20923383117023 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261069957163 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨11, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (20923383117023 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261069957163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_12 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (20914701347587 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565268480539 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨12, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (20914701347587 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565268480539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_13 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41812051444973 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565269484761 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨13, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41812051444973 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565269484761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_14 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83589424932361 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130540977949 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨14, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83589424932361 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130540977949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_15 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (5222173217703 / 6250000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261085920449 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨15, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (5222173217703 / 6250000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261085920449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_16 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83520142508439 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130544977311 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨16, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83520142508439 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130544977311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_17 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (10435692246743 / 12500000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (56527348687 / 2500000000000 : ℝ))
      (E := (cell12623 ⟨17, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (10435692246743 / 12500000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (56527348687 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_18 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (20862739461487 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565274476027 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨18, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (20862739461487 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565274476027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_19 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41708201045407 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261101945839 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨19, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41708201045407 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261101945839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12624_0 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (84077147171941 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565225105931 / 25000000000000 : ℝ))
      (E := (cell12624 ⟨0, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (84077147171941 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565225105931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_1 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (840421477353 / 1000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130452216561 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨1, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (840421477353 / 1000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130452216561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_2 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (84007173267511 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565227102621 / 25000000000000 : ℝ))
      (E := (cell12624 ⟨2, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (84007173267511 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565227102621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_3 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (20993055932999 / 25000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260912422669 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨3, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (20993055932999 / 25000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260912422669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_4 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (8393729909237 / 10000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (70653638143 / 3125000000000 : ℝ))
      (E := (cell12624 ⟨4, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (8393729909237 / 10000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (70653638143 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_5 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (2097559982811 / 2500000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565230103169 / 25000000000000 : ℝ))
      (E := (cell12624 ⟨5, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (2097559982811 / 2500000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565230103169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_6 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41933762178101 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (113046220359 / 5000000000000 : ℝ))
      (E := (cell12624 ⟨6, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41933762178101 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (113046220359 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_7 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41916337093921 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260928412047 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨7, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41916337093921 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260928412047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_8 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41898924385867 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565233094247 / 25000000000000 : ℝ))
      (E := (cell12624 ⟨8, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41898924385867 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565233094247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_9 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83763048072437 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (226093642541 / 10000000000000 : ℝ))
      (E := (cell12624 ⟨9, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83763048072437 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (226093642541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_10 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83728272054699 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (226094039047 / 10000000000000 : ℝ))
      (E := (cell12624 ⟨10, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83728272054699 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (226094039047 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_11 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83693520683449 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130472197547 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨11, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83693520683449 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130472197547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_12 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (418293969619 / 500000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260948387897 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨12, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (418293969619 / 500000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260948387897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_13 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41812045870523 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (282619046907 / 12500000000000 : ℝ))
      (E := (cell12624 ⟨13, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41812045870523 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (282619046907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_14 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (16717882820133 / 20000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260956421431 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨14, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (16717882820133 / 20000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260956421431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_15 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (8355476096831 / 10000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260960416071 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨15, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (8355476096831 / 10000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260960416071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_16 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (10440016538727 / 12500000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260964422921 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨16, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (10440016538727 / 12500000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260964422921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_17 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (10435691011399 / 12500000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (282621048647 / 12500000000000 : ℝ))
      (E := (cell12624 ⟨17, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (10435691011399 / 12500000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (282621048647 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_18 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83450948278627 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260972378139 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨18, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83450948278627 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260972378139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_19 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41708196419241 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130488197361 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨19, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41708196419241 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130488197361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

end BstLean.Part268
