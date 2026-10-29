import BstLean.Part268CellShard24Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12950_20 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (3335161342759 / 4000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444365295757 / 20000000000000 : ℝ))
      (E := (cell12950 ⟨20, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (3335161342759 / 4000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444365295757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_21 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (20836156792921 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110915232071 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨21, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (20836156792921 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110915232071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_22 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (10413780613379 / 12500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (11109172453 / 500000000000 : ℝ))
      (E := (cell12950 ⟨22, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (10413780613379 / 12500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (11109172453 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_23 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83275886742351 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221838503187 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨23, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83275886742351 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221838503187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_24 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83241552645139 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110921252501 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨24, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83241552645139 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110921252501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_25 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41603621291531 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555461624727 / 25000000000000 : ℝ))
      (E := (cell12950 ⟨25, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41603621291531 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555461624727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_26 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (5198309782747 / 6250000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110925243767 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨26, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (5198309782747 / 6250000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110925243767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_27 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41569347217901 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110927265873 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨27, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41569347217901 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110927265873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_28 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83104456286773 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221858516801 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨28, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83104456286773 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221858516801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_29 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41535121022593 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110931251539 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨29, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41535121022593 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110931251539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_30 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83036051679523 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221866550823 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨30, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83036051679523 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221866550823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_31 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83001885158429 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (138866909029 / 6250000000000 : ℝ))
      (E := (cell12950 ⟨31, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83001885158429 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (138866909029 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_32 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41483871225353 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110937271883 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨32, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41483871225353 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110937271883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_33 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (16586724705063 / 20000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555469637439 / 25000000000000 : ℝ))
      (E := (cell12950 ⟨33, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (16586724705063 / 20000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555469637439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_34 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (82899528351377 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (69433830101 / 3125000000000 : ℝ))
      (E := (cell12950 ⟨34, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (82899528351377 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (69433830101 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_35 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41432728449083 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (222188658477 / 10000000000000 : ℝ))
      (E := (cell12950 ⟨35, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41432728449083 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (222188658477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_36 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41415704567557 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444378111209 / 20000000000000 : ℝ))
      (E := (cell12950 ⟨36, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41415704567557 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444378111209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_37 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (82797385031807 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555473648629 / 25000000000000 : ℝ))
      (E := (cell12950 ⟨37, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (82797385031807 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555473648629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_38 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (16552676911597 / 20000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (277737322839 / 12500000000000 : ℝ))
      (E := (cell12950 ⟨38, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (16552676911597 / 20000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (277737322839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_39 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (82729407683541 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221902578997 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨39, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (82729407683541 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221902578997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12951_20 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (20844756287229 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221711010541 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨20, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (20844756287229 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221711010541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_21 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83344619053587 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110857523757 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨21, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83344619053587 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110857523757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_22 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41655118545239 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222171900963 / 10000000000000 : ℝ))
      (E := (cell12951 ⟨22, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41655118545239 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222171900963 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_23 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83275879226921 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (34714422139 / 1562500000000 : ℝ))
      (E := (cell12951 ⟨23, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83275879226921 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (34714422139 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_24 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41620772715207 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (13885794203 / 625000000000 : ℝ))
      (E := (cell12951 ⟨24, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41620772715207 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (13885794203 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_25 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (665657885349 / 800000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110865531237 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨25, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (665657885349 / 800000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110865531237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_26 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (10396618738673 / 12500000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221735047883 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨26, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (10396618738673 / 12500000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221735047883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_27 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83138688120689 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (69429346549 / 3125000000000 : ℝ))
      (E := (cell12951 ⟨27, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83138688120689 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (69429346549 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_28 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83104450270699 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221743072787 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨28, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83104450270699 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221743072787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_29 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (10383779540967 / 12500000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221747057919 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨29, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (10383779540967 / 12500000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221747057919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_30 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (16607209252057 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110875552603 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨30, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (16607209252057 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110875552603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_31 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83001880036989 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110877549539 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨31, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83001880036989 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110877549539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_32 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (20741934406663 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (22217590993 / 1000000000000 : ℝ))
      (E := (cell12951 ⟨32, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (20741934406663 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (22217590993 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_33 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (20733404749559 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (138860194181 / 6250000000000 : ℝ))
      (E := (cell12951 ⟨33, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (20733404749559 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (138860194181 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_34 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41449762060431 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (277720890333 / 12500000000000 : ℝ))
      (E := (cell12951 ⟨34, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41449762060431 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (277720890333 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_35 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41432726481903 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (111088557359 / 5000000000000 : ℝ))
      (E := (cell12951 ⟨35, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41432726481903 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (111088557359 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_36 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (165662810993 / 200000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221775122117 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨36, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (165662810993 / 200000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221775122117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_37 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (8279738168853 / 10000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (444355832987 / 20000000000000 : ℝ))
      (E := (cell12951 ⟨37, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (8279738168853 / 10000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (444355832987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_38 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (82763381509639 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (27772289477 / 1250000000000 : ℝ))
      (E := (cell12951 ⟨38, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (82763381509639 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (27772289477 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_39 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41364702464859 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555446790039 / 25000000000000 : ℝ))
      (E := (cell12951 ⟨39, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41364702464859 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555446790039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12952_20 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (667032133843 / 800000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110797798457 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨20, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (667032133843 / 800000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110797798457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_21 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41672305468487 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444319925447 / 20000000000000 : ℝ))
      (E := (cell12952 ⟨21, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41672305468487 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444319925447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_22 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20827557318843 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (555400895849 / 25000000000000 : ℝ))
      (E := (cell12952 ⟨22, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20827557318843 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (555400895849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_23 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41637935856451 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110803821887 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨23, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41637935856451 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110803821887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_24 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (16648307643413 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110805818209 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨24, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (16648307643413 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110805818209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_25 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83207228755527 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221615622539 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨25, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83207228755527 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221615622539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_26 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83172943296121 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221619663209 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨26, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83172943296121 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221619663209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_27 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (16627736361369 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221623643961 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨27, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (16627736361369 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221623643961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_28 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41552222127929 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (111081381269 / 5000000000000 : ℝ))
      (E := (cell12952 ⟨28, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41552222127929 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (111081381269 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_29 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (16614046122297 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444326333583 / 20000000000000 : ℝ))
      (E := (cell12952 ⟨29, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (16614046122297 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444326333583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_30 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83036040842209 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221635656269 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨30, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83036040842209 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221635656269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_31 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20750468729169 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221639650409 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨31, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20750468729169 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221639650409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_32 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82967732803689 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110821825793 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨32, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82967732803689 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110821825793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_33 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82933614472213 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (277705957603 / 12500000000000 : ℝ))
      (E := (cell12952 ⟨33, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82933614472213 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (277705957603 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_34 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (10362439986421 / 12500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221651678921 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨34, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (10362439986421 / 12500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221651678921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_35 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (2589545282201 / 3125000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (44433114129 / 2000000000000 : ℝ))
      (E := (cell12952 ⟨35, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (2589545282201 / 3125000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (44433114129 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_36 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20707850464709 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110829842543 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨36, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20707850464709 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110829842543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_37 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82797378346169 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444332746457 / 20000000000000 : ℝ))
      (E := (cell12952 ⟨37, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82797378346169 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444332746457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_38 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82763378462173 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (138854233161 / 6250000000000 : ℝ))
      (E := (cell12952 ⟨38, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82763378462173 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (138854233161 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_39 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82729402176741 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (27770896729 / 1250000000000 : ℝ))
      (E := (cell12952 ⟨39, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82729402176741 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (27770896729 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12953_20 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41689504156677 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110740089801 / 50000000000000 : ℝ))
      (E := (cell12953 ⟨20, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41689504156677 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110740089801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_21 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (20836150705461 / 25000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222148420331 / 10000000000000 : ℝ))
      (E := (cell12953 ⟨21, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (20836150705461 / 25000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222148420331 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_22 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83310221461713 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221488211901 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨22, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83310221461713 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221488211901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_23 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (16655172840059 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110746104353 / 50000000000000 : ℝ))
      (E := (cell12953 ⟨23, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (16655172840059 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110746104353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_24 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83241531005091 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221496196819 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨24, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83241531005091 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221496196819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_25 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83207221843769 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221500237523 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨25, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83207221843769 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221500237523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_26 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41586468342081 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555376054157 / 25000000000000 : ℝ))
      (E := (cell12953 ⟨26, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41586468342081 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555376054157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_27 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83138675494269 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (138844265837 / 6250000000000 : ℝ))
      (E := (cell12953 ⟨27, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83138675494269 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (138844265837 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_28 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (332417752969 / 400000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (138844514567 / 6250000000000 : ℝ))
      (E := (cell12953 ⟨28, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (332417752969 / 400000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (138844514567 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_29 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (8307022489643 / 10000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221516274557 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨29, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (8307022489643 / 10000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221516274557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_30 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (16607207085059 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221520262549 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨30, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (16607207085059 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221520262549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_31 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83001869797489 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221524257017 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨31, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83001869797489 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221524257017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_32 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41483863990909 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221528259209 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨32, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41483863990909 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221528259209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_33 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41466804973623 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221532270149 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨33, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41466804973623 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221532270149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_34 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (16579903132579 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221536290633 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨34, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (16579903132579 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221536290633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_35 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (82865445098043 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555385080309 / 25000000000000 : ℝ))
      (E := (cell12953 ⟨35, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (82865445098043 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555385080309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_36 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41415699111061 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222154430363 / 10000000000000 : ℝ))
      (E := (cell12953 ⟨36, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41415699111061 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222154430363 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_37 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (82797375004723 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222154829657 / 10000000000000 : ℝ))
      (E := (cell12953 ⟨37, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (82797375004723 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222154829657 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_38 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (82763375415587 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110776149981 / 50000000000000 : ℝ))
      (E := (cell12953 ⟨38, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (82763375415587 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110776149981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_39 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (2585293732019 / 3125000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222155631349 / 10000000000000 : ℝ))
      (E := (cell12953 ⟨39, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (2585293732019 / 3125000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222155631349 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12954_20 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (1667579997957 / 2000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (222136481691 / 10000000000000 : ℝ))
      (E := (cell12954 ⟨20, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (1667579997957 / 2000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (222136481691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_21 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (20836148677049 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110684417031 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨21, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (20836148677049 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110684417031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_22 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (166620427299 / 200000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444274567359 / 20000000000000 : ℝ))
      (E := (cell12954 ⟨22, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (166620427299 / 200000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444274567359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_23 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41637928344549 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555344207109 / 25000000000000 : ℝ))
      (E := (cell12954 ⟨23, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41637928344549 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555344207109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_24 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83241523794491 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555345217619 / 25000000000000 : ℝ))
      (E := (cell12954 ⟨24, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83241523794491 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555345217619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_25 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (1664144298667 / 2000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444276969801 / 20000000000000 : ℝ))
      (E := (cell12954 ⟨25, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (1664144298667 / 2000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444276969801 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_26 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41586465036753 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555347220867 / 25000000000000 : ℝ))
      (E := (cell12954 ⟨26, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41586465036753 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555347220867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_27 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83138669182961 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444278571879 / 20000000000000 : ℝ))
      (E := (cell12954 ⟨27, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83138669182961 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444278571879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_28 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41552216114937 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110698447931 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨28, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41552216114937 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110698447931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_29 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83070219182573 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221400877843 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨29, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83070219182573 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221400877843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_30 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41518015004771 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221404865511 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨30, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41518015004771 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221404865511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_31 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (20750466169857 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110704459451 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨31, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (20750466169857 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110704459451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_32 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (82967723161037 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221412922169 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨32, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (82967723161037 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221412922169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_33 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41466802711667 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (222141693487 / 10000000000000 : ℝ))
      (E := (cell12954 ⟨33, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41466802711667 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (222141693487 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_34 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41449755717721 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221420899171 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨34, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41449755717721 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221420899171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_35 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (82865441166639 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221424932883 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨35, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (82865441166639 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221424932883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_36 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (82831394586359 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (222142891907 / 10000000000000 : ℝ))
      (E := (cell12954 ⟨36, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (82831394586359 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (222142891907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_37 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (1293708932253 / 1562500000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (277679114561 / 12500000000000 : ℝ))
      (E := (cell12954 ⟨37, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (1293708932253 / 1562500000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (277679114561 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_38 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (2069084309247 / 2500000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221436925041 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨38, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (2069084309247 / 2500000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221436925041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_39 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (2068234916833 / 2500000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555360236103 / 25000000000000 : ℝ))
      (E := (cell12954 ⟨39, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (2068234916833 / 2500000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555360236103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12955_20 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (16675798296773 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555312362633 / 25000000000000 : ℝ))
      (E := (cell12955 ⟨20, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (16675798296773 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555312362633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_21 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (8334458659603 / 10000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (138828341323 / 6250000000000 : ℝ))
      (E := (cell12955 ⟨21, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (8334458659603 / 10000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (138828341323 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_22 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83310205838733 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (13882859113 / 625000000000 : ℝ))
      (E := (cell12955 ⟨22, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83310205838733 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (13882859113 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_23 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83275849179311 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110630751483 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨23, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83275849179311 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110630751483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_24 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83241516585267 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221265482199 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨24, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83241516585267 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221265482199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_25 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83207208024269 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (138829344713 / 6250000000000 : ℝ))
      (E := (cell12955 ⟨25, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83207208024269 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (138829344713 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_26 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (41586461732077 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110636744201 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨26, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (41586461732077 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110636744201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_27 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (2078466571823 / 2500000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110638760219 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨27, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (2078466571823 / 2500000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110638760219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_28 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83104426218731 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (222128149677 / 10000000000000 : ℝ))
      (E := (cell12955 ⟨28, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83104426218731 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (222128149677 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_29 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (10383776683739 / 12500000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (69415173009 / 3125000000000 : ℝ))
      (E := (cell12955 ⟨29, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (10383776683739 / 12500000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (69415173009 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_30 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (1660720491899 / 2000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555322380923 / 25000000000000 : ℝ))
      (E := (cell12955 ⟨30, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (1660720491899 / 2000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555322380923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_31 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83001859562493 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110646759473 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨31, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83001859562493 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110646759473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_32 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82967718341347 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (22212975233 / 1000000000000 : ℝ))
      (E := (cell12955 ⟨32, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82967718341347 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (22212975233 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_33 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (41466800450239 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (88852061511 / 4000000000000 : ℝ))
      (E := (cell12955 ⟨33, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (41466800450239 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (88852061511 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_34 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82899507209009 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221305563167 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨34, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82899507209009 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221305563167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_35 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82865437236219 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (138831850003 / 6250000000000 : ℝ))
      (E := (cell12955 ⟨35, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82865437236219 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (138831850003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_36 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (10353923868943 / 12500000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (277664198761 / 12500000000000 : ℝ))
      (E := (cell12955 ⟨36, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (10353923868943 / 12500000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (277664198761 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_37 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (3311894732983 / 4000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110658796021 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨37, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (3311894732983 / 4000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110658796021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_38 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82763369325053 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (444264321163 / 20000000000000 : ℝ))
      (E := (cell12955 ⟨38, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82763369325053 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (444264321163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_39 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82729393922877 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (138832851943 / 6250000000000 : ℝ))
      (E := (cell12955 ⟨39, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82729393922877 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (138832851943 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12956_20 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83378983071397 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221134138777 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨20, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83378983071397 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221134138777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_21 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (16668915697069 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555284535739 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨21, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (16668915697069 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555284535739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_22 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83310198029413 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (277642766763 / 12500000000000 : ℝ))
      (E := (cell12956 ⟨22, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83310198029413 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (277642766763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_23 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (16655168334187 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555286543481 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨23, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (16655168334187 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555286543481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_24 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83241509377417 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221150148783 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨24, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83241509377417 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221150148783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_25 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (5200450069783 / 6250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221154178311 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨25, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (5200450069783 / 6250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221154178311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_26 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (10396614607013 / 12500000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (55528955169 / 2500000000000 : ℝ))
      (E := (cell12956 ⟨26, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (10396614607013 / 12500000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (55528955169 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_27 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83138656564147 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444232435611 / 20000000000000 : ℝ))
      (E := (cell12956 ⟨27, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83138656564147 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444232435611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_28 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83104420208819 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221166211271 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨28, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83104420208819 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221166211271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_29 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83070207758447 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221170191381 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨29, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83070207758447 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221170191381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_30 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83036019181519 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221174237093 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨30, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83036019181519 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221174237093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_31 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83001854446683 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (222117823283 / 10000000000000 : ℝ))
      (E := (cell12956 ⟨31, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83001854446683 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (222117823283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_32 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41483856761373 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444236447671 / 20000000000000 : ℝ))
      (E := (cell12956 ⟨32, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41483856761373 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444236447671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_33 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (20733399094669 / 25000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110593127343 / 50000000000000 : ℝ))
      (E := (cell12956 ⟨33, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (20733399094669 / 25000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110593127343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_34 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (16579900596719 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221190223991 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨34, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (16579900596719 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221190223991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_35 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (2589544790837 / 3125000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555298566019 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨35, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (2589544790837 / 3125000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555298566019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_36 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (1035392341471 / 1250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444239651601 / 20000000000000 : ℝ))
      (E := (cell12956 ⟨36, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (1035392341471 / 1250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444239651601 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_37 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (5174835311617 / 6250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555300566133 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨37, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (5174835311617 / 6250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555300566133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_38 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (16552673256221 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221206283561 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨38, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (16552673256221 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221206283561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_39 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41364695586639 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (277651282003 / 12500000000000 : ℝ))
      (E := (cell12956 ⟨39, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41364695586639 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (277651282003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12957_20 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83378974660447 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221018823339 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨20, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83378974660447 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221018823339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_21 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41672285188071 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (88840915177 / 4000000000000 : ℝ))
      (E := (cell12957 ⟨21, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41672285188071 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (88840915177 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_22 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83310190221537 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221026864873 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨22, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83310190221537 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221026864873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_23 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (325296227203 / 390625000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (69407213791 / 3125000000000 : ℝ))
      (E := (cell12957 ⟨23, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (325296227203 / 390625000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (69407213791 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_24 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (4162075108547 / 5000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221034870231 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨24, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (4162075108547 / 5000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221034870231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_25 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20801798552531 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110519448069 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨25, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20801798552531 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110519448069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_26 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41586455124679 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221042863213 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨26, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41586455124679 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221042863213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_27 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83138650256641 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110523445357 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨27, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83138650256641 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110523445357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_28 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83104414200139 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110525461191 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨28, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83104414200139 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110525461191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_29 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41535101024089 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444210980327 / 20000000000000 : ℝ))
      (E := (cell12957 ⟨29, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41535101024089 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444210980327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_30 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83036013769249 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (6940809027 / 312500000000 : ℝ))
      (E := (cell12957 ⟨30, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83036013769249 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (6940809027 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_31 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41500924665999 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444212588687 / 20000000000000 : ℝ))
      (E := (cell12957 ⟨31, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41500924665999 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444212588687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_32 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20741927176309 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444213390033 / 20000000000000 : ℝ))
      (E := (cell12957 ⟨32, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20741927176309 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444213390033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_33 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (10366698982241 / 12500000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221070909783 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨33, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (10366698982241 / 12500000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221070909783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_34 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82899498759201 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221074940273 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨34, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82899498759201 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221074940273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_35 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82865429378333 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221078924969 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨35, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82865429378333 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221078924969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_36 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20707845921191 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221082922823 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨36, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20707845921191 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221082922823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_37 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82797361648083 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221086933959 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨37, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82797361648083 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221086933959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_38 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82763363238037 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221090958279 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨38, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82763363238037 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221090958279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_39 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82729388424523 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221094995463 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨39, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82729388424523 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221094995463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12958_20 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83378966251013 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110451781263 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨20, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83378966251013 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110451781263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_21 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (4167228113421 / 5000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (88836302157 / 4000000000000 : ℝ))
      (E := (cell12958 ⟨21, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (4167228113421 / 5000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (88836302157 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_22 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83310182415107 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220911592033 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨22, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83310182415107 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220911592033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_23 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83275826658411 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110457781751 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨23, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83275826658411 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110457781751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_24 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41620747482919 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220919588143 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨24, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41620747482919 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220919588143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_25 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83207187305059 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110461805233 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨25, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83207187305059 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110461805233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_26 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83172903643913 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220927633093 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨26, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83172903643913 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220927633093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_27 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83138643950401 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (44418631999 / 2000000000000 : ℝ))
      (E := (cell12958 ⟨27, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83138643950401 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (44418631999 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_28 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83104408192689 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220935630107 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨28, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83104408192689 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220935630107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_29 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (16614039267821 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110469804269 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨29, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (16614039267821 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110469804269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_30 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41518004179069 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (555235913487 / 25000000000000 : ℝ))
      (E := (cell12958 ⟨30, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41518004179069 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (555235913487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_31 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41500922109219 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220947650761 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨31, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41500922109219 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220947650761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_32 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (16593540777763 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110475829367 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨32, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (16593540777763 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110475829367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_33 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (16586717467647 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (277619459861 / 12500000000000 : ℝ))
      (E := (cell12958 ⟨33, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (16586717467647 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (277619459861 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_34 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (3315979781433 / 4000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220959653387 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨34, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (3315979781433 / 4000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220959653387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_35 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41432712725433 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110481820691 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨35, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41432712725433 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110481820691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_36 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (82831380052797 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220967701897 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨36, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (82831380052797 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220967701897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_37 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (10349669788901 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (138810728689 / 6250000000000 : ℝ))
      (E := (cell12958 ⟨37, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (10349669788901 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (138810728689 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_38 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41381680097923 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (277621961087 / 12500000000000 : ℝ))
      (E := (cell12958 ⟨38, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41381680097923 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (277621961087 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_39 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (82729385676611 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444195934633 / 20000000000000 : ℝ))
      (E := (cell12958 ⟨39, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (82729385676611 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444195934633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12959_20 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (10422369730387 / 12500000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220788298031 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨20, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (10422369730387 / 12500000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220788298031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_21 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83344554162179 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220792341433 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨21, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83344554162179 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220792341433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_22 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83310174610121 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555199078897 / 25000000000000 : ℝ))
      (E := (cell12959 ⟨22, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83310174610121 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555199078897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_23 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41637909577131 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (138800021281 / 6250000000000 : ℝ))
      (E := (cell12959 ⟨23, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41637909577131 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (138800021281 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_24 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (20810371940527 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (55520109023 / 2500000000000 : ℝ))
      (E := (cell12959 ⟨24, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (20810371940527 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (55520109023 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_25 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83207180401331 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110404160649 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨25, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83207180401331 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110404160649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_26 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (8317289703977 / 10000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220812341069 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨26, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (8317289703977 / 10000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220812341069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_27 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (20784659411357 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220816364227 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨27, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (20784659411357 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220816364227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_28 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83104402186471 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220820392933 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨28, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83104402186471 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220820392933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_29 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83070190631227 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220824370603 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨29, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83070190631227 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220824370603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_30 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (20759000737047 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220828357403 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨30, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (20759000737047 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220828357403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_31 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83001839106003 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (277604051671 / 12500000000000 : ℝ))
      (E := (cell12959 ⟨31, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83001839106003 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (277604051671 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_32 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82967699073483 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220836364059 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨32, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82967699073483 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220836364059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_33 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (20733395704899 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220840386179 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨33, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (20733395704899 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220840386179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_34 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82899490313469 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220844421959 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨34, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82899490313469 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220844421959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_35 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82865421524383 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110424206657 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨35, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82865421524383 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110424206657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_36 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41415688210889 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555213104799 / 25000000000000 : ℝ))
      (E := (cell12959 ⟨36, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41415688210889 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555213104799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_37 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41398677487623 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (138803527483 / 6250000000000 : ℝ))
      (E := (cell12959 ⟨37, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41398677487623 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (138803527483 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_38 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (16552671430907 / 20000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555215104021 / 25000000000000 : ℝ))
      (E := (cell12959 ⟨38, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (16552671430907 / 20000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555215104021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_39 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82729382929543 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220864465371 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨39, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82729382929543 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220864465371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12960_20 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (16675789887339 / 20000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220673088163 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨20, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (16675789887339 / 20000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220673088163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_21 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41672273028709 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (88827082679 / 4000000000000 : ℝ))
      (E := (cell12960 ⟨21, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41672273028709 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (88827082679 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_22 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (4165508340329 / 5000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220681093889 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨22, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (4165508340329 / 5000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220681093889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_23 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41637905825761 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220685113923 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨23, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41637905825761 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220685113923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_24 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83241480559751 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220689130167 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨24, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83241480559751 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220689130167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_25 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (4160358674947 / 5000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220693145477 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨25, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (4160358674947 / 5000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220693145477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_26 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83172890436929 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220697104031 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨26, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83172890436929 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220697104031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_27 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83138631341721 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555175281271 / 25000000000000 : ℝ))
      (E := (cell12960 ⟨27, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83138631341721 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555175281271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_28 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83104396181483 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (277588144047 / 12500000000000 : ℝ))
      (E := (cell12960 ⟨28, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83104396181483 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (277588144047 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_29 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (16614036984909 / 20000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220709129319 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨29, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (16614036984909 / 20000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220709129319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_30 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83035997539397 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220713174621 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨30, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83035997539397 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220713174621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_31 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (20750458498673 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220717172699 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨31, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (20750458498673 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220717172699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_32 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (2074192356481 / 2500000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110360591657 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨32, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (2074192356481 / 2500000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110360591657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_33 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82933578302011 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110362574437 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨33, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82933578302011 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110362574437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_34 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (8289948609213 / 10000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444145837473 / 20000000000000 : ℝ))
      (E := (cell12960 ⟨34, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (8289948609213 / 10000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444145837473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_35 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82865417598883 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444146636423 / 20000000000000 : ℝ))
      (E := (cell12960 ⟨35, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82865417598883 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444146636423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_36 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82831372791707 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110368596039 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨36, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82831372791707 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110368596039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_37 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41398675820099 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220741217371 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨37, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41398675820099 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220741217371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_38 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82763354114101 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110372599587 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨38, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82763354114101 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110372599587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_39 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41364690091659 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220749195841 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨39, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41364690091659 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220749195841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12961_20 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83378941031809 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220557874617 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨20, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83378941031809 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220557874617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_21 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (10418067244267 / 12500000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (222056190553 / 10000000000000 : ℝ))
      (E := (cell12961 ⟨21, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (10418067244267 / 12500000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (222056190553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_22 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83310159004483 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (277570733573 / 12500000000000 : ℝ))
      (E := (cell12961 ⟨22, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83310159004483 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (277570733573 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_23 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83275804150191 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (111028494189 / 5000000000000 : ℝ))
      (E := (cell12961 ⟨23, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83275804150191 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (111028494189 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_24 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83241473358767 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220573895881 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨24, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83241473358767 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220573895881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_25 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41603583298943 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (111028895387 / 5000000000000 : ℝ))
      (E := (cell12961 ⟨25, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41603583298943 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (111028895387 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_26 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83172883835389 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110290960989 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨26, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83172883835389 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110290960989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_27 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83138625039279 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220585940987 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨27, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83138625039279 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220585940987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_28 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (3324175607109 / 4000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138786869277 / 6250000000000 : ℝ))
      (E := (cell12961 ⟨28, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (3324175607109 / 4000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138786869277 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_29 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83070179219057 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2775742429 / 125000000000 : ℝ))
      (E := (cell12961 ⟨29, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83070179219057 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2775742429 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_30 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41517996065883 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220597929987 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨30, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41517996065883 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220597929987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_31 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (16600365776901 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110300964377 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨31, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (16600365776901 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110300964377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_32 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41483844723043 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110302970371 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨32, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41483844723043 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110302970371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_33 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41466786892739 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555152491743 / 25000000000000 : ℝ))
      (E := (cell12961 ⟨33, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41466786892739 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555152491743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_34 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (8289948187181 / 10000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110306974801 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨34, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (8289948187181 / 10000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110306974801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_35 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41432706837183 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110309003219 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨35, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41432706837183 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110309003219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_36 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (16566273832517 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220621961861 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨36, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (16566273832517 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220621961861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_37 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41398674153031 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444125198391 / 20000000000000 : ℝ))
      (E := (cell12961 ⟨37, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41398674153031 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444125198391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_38 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41381675537273 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110314989619 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨38, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41381675537273 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110314989619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_39 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82729377437937 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138789627551 / 6250000000000 : ℝ))
      (E := (cell12961 ⟨39, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82729377437937 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138789627551 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12962_20 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83378932628439 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220442715699 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨20, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83378932628439 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220442715699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_21 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41672264926167 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444089348089 / 20000000000000 : ℝ))
      (E := (cell12962 ⟨21, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41672264926167 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444089348089 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_22 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (8331015120383 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555112674507 / 25000000000000 : ℝ))
      (E := (cell12962 ⟨22, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (8331015120383 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555112674507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_23 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83275796650267 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220454708447 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨23, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83275796650267 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220454708447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_24 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (16648293231831 / 20000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (138778669779 / 6250000000000 : ℝ))
      (E := (cell12962 ⟨24, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (16648293231831 / 20000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (138778669779 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_25 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83207159698169 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220462724931 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨25, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83207159698169 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220462724931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_26 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (1663457544703 / 2000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (222046673647 / 10000000000000 : ℝ))
      (E := (cell12962 ⟨26, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (1663457544703 / 2000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (222046673647 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_27 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83138618738103 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220470753469 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨27, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83138618738103 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220470753469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_28 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83104384175197 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220474778087 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨28, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83104384175197 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220474778087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_29 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83070173514763 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (277559844217 / 12500000000000 : ℝ))
      (E := (cell12962 ⟨29, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83070173514763 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (277559844217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_30 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41517993362647 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220482740581 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨30, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41517993362647 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220482740581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_31 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41500911887721 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444097359731 / 20000000000000 : ℝ))
      (E := (cell12962 ⟨31, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41500911887721 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444097359731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_32 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (4148384231701 / 5000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110245376759 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨32, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (4148384231701 / 5000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110245376759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_33 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82933569269999 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555123695467 / 25000000000000 : ℝ))
      (E := (cell12962 ⟨33, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82933569269999 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555123695467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_34 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (20724869413127 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444099765187 / 20000000000000 : ℝ))
      (E := (cell12962 ⟨34, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (20724869413127 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444099765187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_35 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (5179088109427 / 6250000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (222050282763 / 10000000000000 : ℝ))
      (E := (cell12962 ⟨35, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (5179088109427 / 6250000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (222050282763 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_36 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (8283136553441 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220506787229 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨36, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (8283136553441 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220506787229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_37 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82797344972839 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220510822181 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨37, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82797344972839 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220510822181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_38 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (20690837008967 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444102963001 / 20000000000000 : ℝ))
      (E := (cell12962 ⟨38, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (20690837008967 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444102963001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_39 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41364687346699 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110259412029 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨39, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41364687346699 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110259412029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12963_20 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (10422365528323 / 12500000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (138770472069 / 6250000000000 : ℝ))
      (E := (cell12963 ⟨20, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (10422365528323 / 12500000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (138770472069 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_21 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (20836130438003 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (55508289293 / 2500000000000 : ℝ))
      (E := (cell12963 ⟨21, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (20836130438003 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (55508289293 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_22 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (4165507170231 / 5000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220335582219 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨22, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (4165507170231 / 5000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220335582219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_23 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (83275789151751 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220339587921 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨23, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (83275789151751 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220339587921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_24 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (16648291792183 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220343591913 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨24, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (16648291792183 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220343591913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_25 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (20801788199947 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220347597049 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨25, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (20801788199947 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220347597049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_26 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (83172870636211 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220351605949 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨26, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (83172870636211 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220351605949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_27 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (5196163277387 / 6250000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220355620999 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨27, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (5196163277387 / 6250000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220355620999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_28 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41552189086949 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220359585867 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨28, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41552189086949 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220359585867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_29 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (83070167811663 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220363619437 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨29, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (83070167811663 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220363619437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_30 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (4151799065999 / 5000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220367606401 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨30, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (4151799065999 / 5000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220367606401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_31 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41500909333751 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220371606721 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨31, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41500909333751 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220371606721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_32 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41483839911521 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110187810819 / 50000000000000 : ℝ))
      (E := (cell12963 ⟨32, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41483839911521 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110187810819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_33 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82933564755573 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (277547456521 / 12500000000000 : ℝ))
      (E := (cell12963 ⟨33, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82933564755573 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (277547456521 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_34 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (5181217089639 / 6250000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220383640469 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨34, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (5181217089639 / 6250000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220383640469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_35 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (2071635145707 / 2500000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555096911423 / 25000000000000 : ℝ))
      (E := (cell12963 ⟨35, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (2071635145707 / 2500000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555096911423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_36 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82831361907183 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220391668179 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨36, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82831361907183 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220391668179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_37 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82797341640529 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220395649347 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨37, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82797341640529 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220395649347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_38 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82763344998067 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220399647749 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨38, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82763344998067 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220399647749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_39 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82729371949701 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (111020183153 / 5000000000000 : ℝ))
      (E := (cell12963 ⟨39, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82729371949701 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (111020183153 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12964_20 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (20844728956561 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220212445137 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨20, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (20844728956561 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220212445137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_21 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83344513653167 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110108199679 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨21, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83344513653167 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110108199679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_22 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (20827533901713 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220220404459 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨22, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (20827533901713 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220220404459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_23 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41637890827321 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (222022446383 / 10000000000000 : ℝ))
      (E := (cell12964 ⟨23, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41637890827321 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (222022446383 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_24 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41620725882023 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444045692767 / 20000000000000 : ℝ))
      (E := (cell12964 ⟨24, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41620725882023 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444045692767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_25 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41603572951371 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555058116419 / 25000000000000 : ℝ))
      (E := (cell12964 ⟨25, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41603572951371 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555058116419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_26 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83172864038573 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555059117993 / 25000000000000 : ℝ))
      (E := (cell12964 ⟨26, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83172864038573 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555059117993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_27 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (16627721227909 / 20000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (222024048511 / 10000000000000 : ℝ))
      (E := (cell12964 ⟨27, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (16627721227909 / 20000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (222024048511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_28 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83104372173829 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444048889751 / 20000000000000 : ℝ))
      (E := (cell12964 ⟨28, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83104372173829 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444048889751 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_29 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83070162109757 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (135513213 / 6103515625 : ℝ))
      (E := (cell12964 ⟨29, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83070162109757 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (135513213 / 6103515625 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_30 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (5189748494739 / 6250000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (138765779307 / 6250000000000 : ℝ))
      (E := (cell12964 ⟨30, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (5189748494739 / 6250000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (138765779307 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_31 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (16600362712137 / 20000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220256470073 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨31, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (16600362712137 / 20000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220256470073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_32 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (2592739844161 / 3125000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220260486521 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨32, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (2592739844161 / 3125000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220260486521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_33 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (414667801211 / 500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110132259633 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨33, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (414667801211 / 500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110132259633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_34 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82899469216957 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220268510469 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨34, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82899469216957 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220268510469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_35 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (8286540190671 / 10000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220272519279 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨35, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (8286540190671 / 10000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220272519279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_36 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82831358280903 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444055309207 / 20000000000000 : ℝ))
      (E := (cell12964 ⟨36, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82831358280903 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444055309207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_37 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (8279733830913 / 10000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220280532157 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨37, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (8279733830913 / 10000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220280532157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_38 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (10345417745143 / 12500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444056907239 / 20000000000000 : ℝ))
      (E := (cell12964 ⟨38, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (10345417745143 / 12500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444056907239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_39 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82729369206847 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (8673002179 / 390625000000 : ℝ))
      (E := (cell12964 ⟨39, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82729369206847 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (8673002179 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12965_20 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41689453713709 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110048666749 / 50000000000000 : ℝ))
      (E := (cell12965 ⟨20, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41689453713709 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110048666749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_21 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41672252777901 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220101340013 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨21, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41672252777901 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220101340013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_22 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (2603441494079 / 3125000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220105339799 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨22, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (2603441494079 / 3125000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220105339799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_23 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83275774158939 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220109336177 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨23, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83275774158939 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220109336177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_24 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (20810361142137 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220113332231 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨24, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (20810361142137 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220113332231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_25 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (10400892375879 / 12500000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220117330813 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨25, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (10400892375879 / 12500000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220117330813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_26 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16634571488447 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220121334541 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨26, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16634571488447 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220121334541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_27 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83138599842163 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220125345803 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨27, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83138599842163 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220125345803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_28 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83104366174989 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (69379042711 / 3125000000000 : ℝ))
      (E := (cell12965 ⟨28, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83104366174989 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (69379042711 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_29 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16614031281809 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220133340801 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨29, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16614031281809 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220133340801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_30 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83035970512827 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220137386651 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨30, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83035970512827 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220137386651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_31 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (8300180845499 / 10000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (555035347179 / 25000000000000 : ℝ))
      (E := (cell12965 ⟨31, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (8300180845499 / 10000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (555035347179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_32 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (1659353404087 / 2000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220145406751 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨32, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (1659353404087 / 2000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220145406751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_33 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41466777864939 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444029876633 / 20000000000000 : ℝ))
      (E := (cell12965 ⟨33, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41466777864939 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444029876633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_34 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82899465000707 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444030675461 / 20000000000000 : ℝ))
      (E := (cell12965 ⟨34, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82899465000707 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444030675461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_35 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82865397986123 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (277519673717 / 12500000000000 : ℝ))
      (E := (cell12965 ⟨35, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82865397986123 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (277519673717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_36 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82831354655569 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (173450111 / 7812500000 : ℝ))
      (E := (cell12965 ⟨36, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82831354655569 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (173450111 / 7812500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_37 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (20699333744661 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220165411911 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨37, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (20699333744661 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220165411911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_38 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82763338925097 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220169421621 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨38, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82763338925097 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220169421621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_39 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16545873292967 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220173449603 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨39, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16545873292967 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220173449603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12966_20 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (16675779806021 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1109991109093 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨20, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (16675779806021 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1109991109093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_21 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41672248729957 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (443997243741 / 20000000000000 : ℝ))
      (E := (cell12966 ⟨21, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41672248729957 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (443997243741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_22 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (16662024003129 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (110999513577 / 5000000000000 : ℝ))
      (E := (cell12966 ⟨22, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (16662024003129 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (110999513577 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_23 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (20818941666161 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219994263333 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨23, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (20818941666161 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219994263333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_24 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83241437374421 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219998255497 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨24, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83241437374421 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219998255497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_25 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83207132112657 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220002250881 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨25, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83207132112657 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220002250881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_26 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (20793212711799 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110003126051 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨26, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (20793212711799 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110003126051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_27 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (16627718709209 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220010261547 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨27, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (16627718709209 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220010261547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_28 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83104360177377 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (222001428137 / 10000000000000 : ℝ))
      (E := (cell12966 ⟨28, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83104360177377 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (222001428137 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_29 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41535075354763 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (444003662699 / 20000000000000 : ℝ))
      (E := (cell12966 ⟨29, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41535075354763 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (444003662699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_30 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (20758991277747 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220022301081 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨30, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (20758991277747 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220022301081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_31 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83001803350419 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (444005260817 / 20000000000000 : ℝ))
      (E := (cell12966 ⟨31, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83001803350419 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (444005260817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_32 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41483832698317 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220030323747 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨32, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41483832698317 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220030323747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_33 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82933551218609 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220034302471 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨33, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82933551218609 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220034302471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_34 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41449730392737 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (277504787451 / 12500000000000 : ℝ))
      (E := (cell12966 ⟨34, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41449730392737 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (277504787451 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_35 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82865394066517 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110021157861 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨35, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82865394066517 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110021157861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_36 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82831351031183 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (44400927023 / 2000000000000 : ℝ))
      (E := (cell12966 ⟨36, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82831351031183 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (44400927023 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_37 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82797331649069 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (222005034731 / 10000000000000 : ℝ))
      (E := (cell12966 ⟨37, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82797331649069 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (222005034731 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_38 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (10345416986241 / 12500000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220054362751 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨38, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (10345416986241 / 12500000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220054362751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_39 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (5170585232729 / 6250000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110029169199 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨39, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (5170585232729 / 6250000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110029169199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12967_20 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41689445317153 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109933578753 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨20, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41689445317153 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109933578753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_21 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (5086943931 / 6103515625 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219871152089 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨21, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (5086943931 / 6103515625 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219871152089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_22 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16662022444441 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109937599841 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨22, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16662022444441 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109937599841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_23 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41637879585877 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219879186929 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨23, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41637879585877 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219879186929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_24 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16648286036333 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109941587619 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨24, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16648286036333 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109941587619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_25 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83207125219617 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219887225881 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨25, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83207125219617 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219887225881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_26 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (5198302765841 / 6250000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109945612327 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨26, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (5198302765841 / 6250000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109945612327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_27 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (8313858725119 / 10000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219895232343 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨27, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (8313858725119 / 10000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219895232343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_28 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83104354180993 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219899251099 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨28, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83104354180993 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219899251099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_29 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83070145011199 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219903224333 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨29, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83070145011199 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219903224333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_30 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16607191942061 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109953606103 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨30, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16607191942061 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109953606103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_31 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83001798246969 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219911216183 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨31, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83001798246969 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219911216183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_32 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41483830295003 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109957618753 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨32, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41483830295003 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109957618753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_33 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82933546708391 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219919277187 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨33, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82933546708391 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219919277187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_34 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82899456571257 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219923277381 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨34, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82899456571257 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219923277381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_35 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82865390147893 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443985459447 / 20000000000000 : ℝ))
      (E := (cell12967 ⟨35, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82865390147893 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443985459447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_36 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41415673703871 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (221993127841 / 10000000000000 : ℝ))
      (E := (cell12967 ⟨36, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41415673703871 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (221993127841 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_37 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16559465664081 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109967639827 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨37, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16559465664081 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109967639827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_38 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41381666427817 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109969650431 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨38, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41381666427817 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109969650431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_39 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16545872196667 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109971641479 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨39, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16545872196667 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109971641479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12968_20 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83378882240021 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109876075729 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨20, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83378882240021 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109876075729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_21 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83344481272571 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443951228033 / 20000000000000 : ℝ))
      (E := (cell12968 ⟨21, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83344481272571 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443951228033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_22 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (16662020886041 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (554940031057 / 25000000000000 : ℝ))
      (E := (cell12968 ⟨22, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (16662020886041 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (554940031057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_23 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (8327575168027 / 10000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219764165337 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨23, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (8327575168027 / 10000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219764165337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_24 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83241422990279 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219768149851 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨24, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83241422990279 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219768149851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_25 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (10400889790989 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219772197391 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨25, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (10400889790989 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219772197391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_26 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (16634567532203 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443955238751 / 20000000000000 : ℝ))
      (E := (cell12968 ⟨26, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (16634567532203 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443955238751 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_27 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83138580957599 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219780199723 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨27, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83138580957599 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219780199723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_28 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83104348185837 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219784217449 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨28, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83104348185837 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219784217449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_29 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (16614027862813 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219788190341 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨29, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (16614027862813 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219788190341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_30 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83035954310781 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (3468425279 / 156250000000 : ℝ))
      (E := (cell12968 ⟨30, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83035954310781 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (3468425279 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_31 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83001793144641 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219796183573 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨31, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83001793144641 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219796183573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_32 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (5185478486529 / 6250000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219800206617 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨32, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (5185478486529 / 6250000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219800206617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_33 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (3317341687969 / 4000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (17342220693 / 781250000000 : ℝ))
      (E := (cell12968 ⟨33, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (3317341687969 / 4000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (17342220693 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_34 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (82899452358057 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (221980825199 / 10000000000000 : ℝ))
      (E := (cell12968 ⟨34, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (82899452358057 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (221980825199 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_35 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (82865386230249 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219812216967 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨35, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (82865386230249 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219812216967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_36 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (2588479493289 / 3125000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109908130629 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨36, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (2588479493289 / 3125000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109908130629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_37 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (82797324992653 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443964053529 / 20000000000000 : ℝ))
      (E := (cell12968 ⟨37, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (82797324992653 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443964053529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_38 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (82763329822217 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109912117977 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨38, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (82763329822217 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109912117977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_39 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (82729358243847 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219828283283 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨39, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (82729358243847 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219828283283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12969_20 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (5211179615453 / 6250000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (110981857087 / 5000000000000 : ℝ))
      (E := (cell12969 ⟨20, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (5211179615453 / 6250000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (110981857087 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_21 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (16668894636223 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219641124609 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨21, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (16668894636223 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219641124609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_22 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83310096639647 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109822580939 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨22, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83310096639647 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109822580939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_23 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83275744190191 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109824570093 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨23, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83275744190191 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109824570093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_24 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41620707900131 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219653179339 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨24, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41620707900131 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219653179339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_25 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (4160355571877 / 5000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (277457145677 / 12500000000000 : ℝ))
      (E := (cell12969 ⟨25, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (4160355571877 / 5000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (277457145677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_26 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83172831069873 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (443932231881 / 20000000000000 : ℝ))
      (E := (cell12969 ⟨26, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83172831069873 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (443932231881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_27 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83138574665271 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219665163689 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨27, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83138574665271 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219665163689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_28 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83104342191909 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (110983459021 / 5000000000000 : ℝ))
      (E := (cell12969 ⟨28, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83104342191909 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (110983459021 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_29 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83070133618123 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109836605761 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨29, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83070133618123 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109836605761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_30 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (20758987228103 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (554919300037 / 25000000000000 : ℝ))
      (E := (cell12969 ⟨30, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (20758987228103 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (554919300037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_31 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (16600357608687 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109840603127 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨31, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (16600357608687 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109840603127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_32 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (10370956372501 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219685231079 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨32, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (10370956372501 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219685231079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_33 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82933537691109 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109844608513 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨33, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82933537691109 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109844608513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_34 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (5181215509117 / 6250000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (27746165293 / 1250000000000 : ℝ))
      (E := (cell12969 ⟨34, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (5181215509117 / 6250000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (27746165293 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_35 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82865382313587 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219697250883 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨35, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82865382313587 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219697250883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_36 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (828313401637 / 1000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (443940248203 / 20000000000000 : ℝ))
      (E := (cell12969 ⟨36, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (828313401637 / 1000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (443940248203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_37 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82797321665811 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219705252583 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨37, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82797321665811 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219705252583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_38 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (20690831697419 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219709226753 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨38, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (20690831697419 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219709226753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_39 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82729355505201 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (3551541249 / 160000000000 : ℝ))
      (E := (cell12969 ⟨39, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82729355505201 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (3551541249 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12970_20 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83378865455987 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443904425671 / 20000000000000 : ℝ))
      (E := (cell12970 ⟨20, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83378865455987 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443904425671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_21 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (1302257267049 / 1562500000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554881540937 / 25000000000000 : ℝ))
      (E := (cell12970 ⟨21, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (1302257267049 / 1562500000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554881540937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_22 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (8331008885053 / 10000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109765068791 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨22, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (8331008885053 / 10000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109765068791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_23 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41637868350759 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219534169849 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨23, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41637868350759 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219534169849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_24 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (16648281722323 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219538146907 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨24, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (16648281722323 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219538146907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_25 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83207104548503 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (277442773547 / 12500000000000 : ℝ))
      (E := (cell12970 ⟨25, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83207104548503 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (277442773547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_26 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83172824480029 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (44390923601 / 2000000000000 : ℝ))
      (E := (cell12970 ⟨26, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83172824480029 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (44390923601 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_27 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41569284187103 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (221955018271 / 10000000000000 : ℝ))
      (E := (cell12970 ⟨27, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41569284187103 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (221955018271 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_28 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (10388042024901 / 12500000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219554198507 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨28, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (10388042024901 / 12500000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219554198507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_29 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41535063961687 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109779114681 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨29, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41535063961687 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109779114681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_30 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83035943515201 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219562218431 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨30, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83035943515201 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219562218431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_31 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (1660035658867 / 2000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554891556417 / 25000000000000 : ℝ))
      (E := (cell12970 ⟨31, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (1660035658867 / 2000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554891556417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_32 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (82967646176639 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219570252309 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨32, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (82967646176639 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219570252309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_33 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (16586706636809 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109787120379 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨33, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (16586706636809 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109787120379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_34 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (82899443934703 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219578250361 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨34, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (82899443934703 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219578250361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_35 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (16573075679581 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219582223021 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨35, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (16573075679581 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219582223021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_36 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (82831336543097 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554896569091 / 25000000000000 : ℝ))
      (E := (cell12970 ⟨36, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (82831336543097 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554896569091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_37 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (2069932958497 / 2500000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219590234469 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨37, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (2069932958497 / 2500000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219590234469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_38 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (8276332375801 / 10000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109797136631 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨38, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (8276332375801 / 10000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109797136631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_39 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (16545870553479 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219598274987 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨39, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (16545870553479 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219598274987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12971_20 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41689428533119 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443881433921 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨20, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41689428533119 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443881433921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_21 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (10418057125329 / 12500000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277426399907 / 12500000000000 : ℝ))
      (E := (cell12971 ⟨21, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (10418057125329 / 12500000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277426399907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_22 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83310081062853 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277426903299 / 12500000000000 : ℝ))
      (E := (cell12971 ⟨22, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83310081062853 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277426903299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_23 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83275729214249 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443883839191 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨23, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83275729214249 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443883839191 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_24 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83241401424337 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219423227749 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨24, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83241401424337 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219423227749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_25 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83207097660799 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (44388544157 / 2000000000000 : ℝ))
      (E := (cell12971 ⟨25, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83207097660799 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (44388544157 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_26 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83172817891483 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109715598623 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨26, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83172817891483 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109715598623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_27 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83138562084403 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109717628393 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨27, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83138562084403 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109717628393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_28 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41552165103867 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219439213217 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨28, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41552165103867 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219439213217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_29 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (16614024445963 / 20000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219443243863 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨29, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (16614024445963 / 20000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219443243863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_30 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41517969059573 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (221944723341 / 10000000000000 : ℝ))
      (E := (cell12971 ⟨30, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41517969059573 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (221944723341 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_31 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41500888922193 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219451241813 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨31, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41500888922193 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219451241813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_32 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (16593528274871 / 20000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219455270307 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨32, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (16593528274871 / 20000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219455270307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_33 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82933528678031 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443891852259 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨33, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82933528678031 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443891852259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_34 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (1657988794491 / 2000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219463274121 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨34, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (1657988794491 / 2000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219463274121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_35 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (20716343620801 / 25000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (69358353417 / 3125000000000 : ℝ))
      (E := (cell12971 ⟨35, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (20716343620801 / 25000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (69358353417 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_36 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (1035391661543 / 1250000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (138716956789 / 6250000000000 : ℝ))
      (E := (cell12971 ⟨36, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (1035391661543 / 1250000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (138716956789 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_37 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (4139865750743 / 5000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443895066141 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨37, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (4139865750743 / 5000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443895066141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_38 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (4138166036361 / 5000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219479316753 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨38, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (4138166036361 / 5000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219479316753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_39 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (8272935003043 / 10000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (554870831279 / 25000000000000 : ℝ))
      (E := (cell12971 ⟨39, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (8272935003043 / 10000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (554870831279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12972_20 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16675768587973 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219292231497 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨20, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16675768587973 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219292231497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_21 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83344442894789 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219296244191 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨21, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83344442894789 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219296244191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_22 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83310066973517 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109650127217 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨22, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83310066973517 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109650127217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_23 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83275715143397 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219304265541 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨23, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83275715143397 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219304265541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_24 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83241387371947 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219308280593 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨24, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83241387371947 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219308280593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_25 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (2600221363339 / 3125000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554828075609 / 25000000000000 : ℝ))
      (E := (cell12972 ⟨25, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (2600221363339 / 3125000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554828075609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_26 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (1663456077519 / 2000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219316275239 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨26, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (1663456077519 / 2000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219316275239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_27 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16627709617453 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (8877281273 / 400000000000 : ℝ))
      (E := (cell12972 ⟨27, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16627709617453 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (8877281273 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_28 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83104316228969 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219324316707 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨28, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83104316228969 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219324316707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_29 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (415350541347 / 500000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (88773133239 / 4000000000000 : ℝ))
      (E := (cell12972 ⟨29, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (415350541347 / 500000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (88773133239 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_30 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83035924177059 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109666152103 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨30, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83035924177059 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109666152103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_31 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16600352784121 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554834074089 / 25000000000000 : ℝ))
      (E := (cell12972 ⟨31, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16600352784121 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554834074089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_32 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (41483813734429 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219340308661 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨32, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (41483813734429 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219340308661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_33 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82933514790797 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219344342129 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨33, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82933514790797 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219344342129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_34 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (20724856463889 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (443869667783 / 20000000000000 : ℝ))
      (E := (cell12972 ⟨34, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (20724856463889 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (443869667783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_35 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (20716340158107 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109676179081 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨35, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (20716340158107 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109676179081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_36 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (4141565954543 / 5000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (277419542691 / 12500000000000 : ℝ))
      (E := (cell12972 ⟨36, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (4141565954543 / 5000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (277419542691 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_37 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16559460240091 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219360347757 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨37, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16559460240091 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219360347757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_38 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (10345413366371 / 12500000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109682188371 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨38, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (10345413366371 / 12500000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109682188371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_39 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82729336252309 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219368369403 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨39, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82729336252309 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219368369403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12973_20 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (3335153142719 / 4000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219177361819 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨20, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (3335153142719 / 4000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219177361819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_21 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83344428529223 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219181369691 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨21, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83344428529223 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219181369691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_22 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (8331005261427 / 10000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109592687579 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨22, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (8331005261427 / 10000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109592687579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_23 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83275700790463 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219189381537 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨23, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83275700790463 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219189381537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_24 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83241373025321 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (554798333377 / 25000000000000 : ℝ))
      (E := (cell12973 ⟨24, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83241373025321 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (554798333377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_25 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (3328282771461 / 4000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (554799337673 / 25000000000000 : ℝ))
      (E := (cell12973 ⟨25, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (3328282771461 / 4000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (554799337673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_26 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (20793197385481 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219201377327 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨26, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (20793197385481 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219201377327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_27 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (8313853375953 / 10000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219205357327 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨27, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (8313853375953 / 10000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219205357327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_28 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83104301907521 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (443841881951 / 20000000000000 : ℝ))
      (E := (cell12973 ⟨28, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83104301907521 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (443841881951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_29 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83070093954233 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219213419573 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨29, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83070093954233 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219213419573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_30 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (10379488733521 / 12500000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219217388399 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨30, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (10379488733521 / 12500000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219217388399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_31 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (16600349923597 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109610717377 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨31, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (16600349923597 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109610717377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_32 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (10370951646563 / 12500000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221922544277 / 10000000000000 : ℝ))
      (E := (cell12973 ⟨32, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (10370951646563 / 12500000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221922544277 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_33 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41466750250351 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219229413389 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨33, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41466750250351 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219229413389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_34 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (20724852892929 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (554808351489 / 25000000000000 : ℝ))
      (E := (cell12973 ⟨34, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (20724852892929 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (554808351489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_35 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41432673177419 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219237421029 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨35, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41432673177419 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219237421029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_36 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (16566260963903 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219241458947 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨36, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (16566260963903 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219241458947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_37 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (82797286935349 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (3467571033 / 156250000000 : ℝ))
      (E := (cell12973 ⟨37, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (82797286935349 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (3467571033 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_38 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (2586352896003 / 3125000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109624743047 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨38, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (2586352896003 / 3125000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109624743047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_39 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41364660999833 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221925347479 / 10000000000000 : ℝ))
      (E := (cell12973 ⟨39, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41364660999833 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221925347479 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12974_20 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83378814198303 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443812485889 / 20000000000000 : ℝ))
      (E := (cell12974 ⟨20, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83378814198303 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443812485889 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_21 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (666755313327 / 800000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (277383304059 / 12500000000000 : ℝ))
      (E := (cell12974 ⟨21, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (666755313327 / 800000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (277383304059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_22 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83310038257239 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109535245747 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨22, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83310038257239 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109535245747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_23 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16655137287949 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (277384311643 / 12500000000000 : ℝ))
      (E := (cell12974 ⟨23, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16655137287949 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (277384311643 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_24 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83241358680909 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (138692406177 / 6250000000000 : ℝ))
      (E := (cell12974 ⟨24, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83241358680909 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (138692406177 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_25 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16641410989683 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219082452983 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨25, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16641410989683 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219082452983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_26 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (8317277521011 / 10000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219086475029 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨26, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (8317277521011 / 10000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219086475029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_27 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (10392314929251 / 12500000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443818101791 / 20000000000000 : ℝ))
      (E := (cell12974 ⟨27, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (10392314929251 / 12500000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443818101791 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_28 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20776071897071 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219094498419 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨28, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20776071897071 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219094498419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_29 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83070079641277 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109549251893 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨29, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83070079641277 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109549251893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_30 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (41517947780743 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219102526749 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨30, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (41517947780743 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219102526749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_31 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83001735317573 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219106510207 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨31, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83001735317573 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219106510207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_32 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20741899719589 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109555256957 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨32, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20741899719589 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109555256957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_33 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82933486212813 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219114538877 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨33, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82933486212813 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219114538877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_34 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82899397290081 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219118527249 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨34, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82899397290081 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219118527249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_35 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20716333019863 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109561269087 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨35, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20716333019863 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109561269087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_36 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20707822637593 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (221912657199 / 10000000000000 : ℝ))
      (E := (cell12974 ⟨36, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20707822637593 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (221912657199 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_37 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16559454534489 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109565285053 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨37, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16559454534489 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109565285053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_38 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (3310531136617 / 4000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219134591071 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨38, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (3310531136617 / 4000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219134591071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_39 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82729307749223 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554784643951 / 25000000000000 : ℝ))
      (E := (cell12974 ⟨39, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82729307749223 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554784643951 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

end BstLean.Part268
