import BstLean.Part268CellShard21Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12875_0 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (21018344706783 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230477608901 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨0, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (21018344706783 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230477608901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_1 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (10504807406403 / 12500000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230481601329 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨1, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (10504807406403 / 12500000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230481601329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_2 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (4200178226563 / 5000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230485576367 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨2, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (4200178226563 / 5000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230485576367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_3 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (164001356701 / 195312500000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (44609792009 / 2000000000000 : ℝ))
      (E := (cell12875 ⟨3, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (164001356701 / 195312500000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (44609792009 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_4 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83933849514041 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230493566087 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨4, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83933849514041 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230493566087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_5 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (41949514572351 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230497597117 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨5, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (41949514572351 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230497597117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_6 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83864233487133 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557625396361 / 25000000000000 : ℝ))
      (E := (cell12875 ⟨6, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83864233487133 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557625396361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_7 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (20957365626441 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115252798251 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨7, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (20957365626441 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115252798251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_8 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83794716165209 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (111525478977 / 5000000000000 : ℝ))
      (E := (cell12875 ⟨8, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83794716165209 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (111525478977 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_9 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (20939998607567 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230513599533 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨9, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (20939998607567 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230513599533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_10 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (20931324316481 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230517605181 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨10, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (20931324316481 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230517605181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_11 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83690624637343 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115260801461 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨11, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83690624637343 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115260801461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_12 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (5228498531867 / 6250000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (44610511979 / 2000000000000 : ℝ))
      (E := (cell12875 ⟨12, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (5228498531867 / 6250000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (44610511979 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_13 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (41810676424519 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (223052959921 / 10000000000000 : ℝ))
      (E := (cell12875 ⟨13, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (41810676424519 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (223052959921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_14 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83586753620549 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230533609399 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨14, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83586753620549 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230533609399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_15 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83552178790289 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230537634971 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨15, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83552178790289 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230537634971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_16 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83517628324319 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (446108324587 / 20000000000000 : ℝ))
      (E := (cell12875 ⟨16, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83517628324319 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (446108324587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_17 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (20870775547219 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (446109127283 / 20000000000000 : ℝ))
      (E := (cell12875 ⟨17, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (20870775547219 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (446109127283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_18 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83448600350371 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230549621887 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨18, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83448600350371 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230549621887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_19 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83414122775391 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115276821019 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨19, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83414122775391 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115276821019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12876_0 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (21018341027003 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230360213357 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨0, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (21018341027003 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230360213357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_1 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (5252402802841 / 6250000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (223036418109 / 10000000000000 : ℝ))
      (E := (cell12876 ⟨1, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (5252402802841 / 6250000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (223036418109 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_2 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (42001775219201 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278796023753 / 12500000000000 : ℝ))
      (E := (cell12876 ⟨2, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (42001775219201 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278796023753 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_3 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41984340425261 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230372190869 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨3, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41984340425261 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230372190869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_4 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83933836045679 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (69699255997 / 3125000000000 : ℝ))
      (E := (cell12876 ⟨4, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83933836045679 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (69699255997 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_5 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83899015987927 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230380201149 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨5, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83899015987927 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230380201149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_6 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (20966055160377 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230384226371 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨6, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (20966055160377 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230384226371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_7 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (1676588999417 / 2000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446077643419 / 20000000000000 : ℝ))
      (E := (cell12876 ⟨7, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (1676588999417 / 2000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446077643419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_8 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (8379470394057 / 10000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230392238523 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨8, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (8379470394057 / 10000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230392238523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_9 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (20939995628867 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115198119813 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨9, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (20939995628867 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115198119813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_10 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (5232830353783 / 6250000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115200113547 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨10, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (5232830353783 / 6250000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115200113547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_11 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (20922653335229 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115202103683 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨11, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (20922653335229 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115202103683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_12 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41827982760991 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230408244739 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨12, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41827982760991 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230408244739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_13 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83621342169253 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230412228967 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨13, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83621342169253 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230412228967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_14 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41793371624219 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230416223829 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨14, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41793371624219 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230416223829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_15 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83552168725421 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230420234781 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨15, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83552168725421 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230420234781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_16 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (10439702320783 / 12500000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278803033379 / 12500000000000 : ℝ))
      (E := (cell12876 ⟨16, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (10439702320783 / 12500000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278803033379 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_17 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41741546368603 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230428267323 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨17, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41741546368603 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230428267323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_18 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83448591204659 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230432240309 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨18, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83448591204659 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230432240309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_19 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83414113935209 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230436248677 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨19, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83414113935209 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230436248677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12877_0 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (42036674695591 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (139390175831 / 6250000000000 : ℝ))
      (E := (cell12877 ⟨0, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (42036674695591 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (139390175831 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_1 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (4201921522097 / 5000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115123436037 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨1, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (4201921522097 / 5000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115123436037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_2 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (42001768173879 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557562714279 / 25000000000000 : ℝ))
      (E := (cell12877 ⟨2, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (42001768173879 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557562714279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_3 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (20992166768077 / 25000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (446050966957 / 20000000000000 : ℝ))
      (E := (cell12877 ⟨3, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (20992166768077 / 25000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (446050966957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_4 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (327866494451 / 390625000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115129435639 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨4, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (327866494451 / 390625000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115129435639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_5 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41949501416627 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (5575657147 / 250000000000 : ℝ))
      (E := (cell12877 ⟨5, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41949501416627 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (5575657147 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_6 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83864207797947 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230266863013 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨6, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83864207797947 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230266863013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_7 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83829437437963 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230270833439 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨7, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83829437437963 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230270833439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_8 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83794691717921 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230274835281 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨8, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83794691717921 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230274835281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_9 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (4187998530131 / 5000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557569718887 / 25000000000000 : ℝ))
      (E := (cell12877 ⟨9, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (4187998530131 / 5000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557569718887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_10 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83725274057047 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115141422437 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨10, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83725274057047 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115141422437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_11 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (2615331313949 / 3125000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115143432899 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨11, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (2615331313949 / 3125000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115143432899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_12 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41827977267967 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (223029088647 / 10000000000000 : ℝ))
      (E := (cell12877 ⟨12, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41827977267967 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (223029088647 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_13 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83621331491273 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115147427351 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨13, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83621331491273 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115147427351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_14 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41793366439047 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (139393680777 / 6250000000000 : ℝ))
      (E := (cell12877 ⟨14, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41793366439047 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (139393680777 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_15 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83552158662283 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (89212115553 / 4000000000000 : ℝ))
      (E := (cell12877 ⟨15, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83552158662283 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (89212115553 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_16 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (5219850550619 / 6250000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230306907221 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨16, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (5219850550619 / 6250000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230306907221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_17 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41741541643597 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230310894361 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨17, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41741541643597 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230310894361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_18 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (10431072757571 / 12500000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557578728287 / 25000000000000 : ℝ))
      (E := (cell12877 ⟨18, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (10431072757571 / 12500000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557578728287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_19 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83414105096611 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230318909793 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨19, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83414105096611 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230318909793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12878_0 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (84073334676639 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (3568200839 / 160000000000 : ℝ))
      (E := (cell12878 ⟨0, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (84073334676639 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (3568200839 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_1 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (3361536641627 / 4000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230129500729 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨1, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (3361536641627 / 4000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230129500729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_2 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (84003522259327 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (278766689971 / 12500000000000 : ℝ))
      (E := (cell12878 ⟨2, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (84003522259327 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (278766689971 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_3 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83968653296271 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557534383049 / 25000000000000 : ℝ))
      (E := (cell12878 ⟨3, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83968653296271 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557534383049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_4 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83933809115371 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (223014154629 / 10000000000000 : ℝ))
      (E := (cell12878 ⟨4, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83933809115371 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (223014154629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_5 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41949494840341 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230145512127 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨5, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41949494840341 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230145512127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_6 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (1677283899129 / 2000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (278768694167 / 12500000000000 : ℝ))
      (E := (cell12878 ⟨6, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (1677283899129 / 2000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (278768694167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_7 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83829424907103 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115076751763 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨7, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83829424907103 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115076751763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_8 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83794679497261 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230157543859 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨8, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83794679497261 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230157543859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_9 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (3350398347669 / 4000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230161507297 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨9, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (3350398347669 / 4000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230161507297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_10 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83725262455481 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115082758291 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨10, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83725262455481 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115082758291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_11 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83690590753699 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230169520133 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨11, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83690590753699 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230169520133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_12 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83655943551727 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115086762071 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨12, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83655943551727 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115086762071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_13 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83621320815097 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (44603550691 / 2000000000000 : ℝ))
      (E := (cell12878 ⟨13, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83621320815097 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (44603550691 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_14 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41793361254759 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230181557053 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨14, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41793361254759 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230181557053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_15 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83552148600877 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557546384731 / 25000000000000 : ℝ))
      (E := (cell12878 ⟨15, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83552148600877 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557546384731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_16 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83517599055237 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (139386846469 / 6250000000000 : ℝ))
      (E := (cell12878 ⟨16, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83517599055237 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (139386846469 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_17 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83483073838839 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557548393939 / 25000000000000 : ℝ))
      (E := (cell12878 ⟨17, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83483073838839 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557548393939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_18 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83448572918097 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (446039516431 / 20000000000000 : ℝ))
      (E := (cell12878 ⟨18, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83448572918097 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (446039516431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_19 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83414096259597 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557550391779 / 25000000000000 : ℝ))
      (E := (cell12878 ⟨19, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83414096259597 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557550391779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12879_0 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (16814663992877 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230008230937 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨0, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (16814663992877 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230008230937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_1 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (4201920082083 / 5000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115006091379 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨1, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (4201920082083 / 5000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115006091379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_2 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (84003508173109 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (139376014741 / 6250000000000 : ℝ))
      (E := (cell12879 ⟨2, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (84003508173109 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (139376014741 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_3 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83968639522409 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230020225207 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨3, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83968639522409 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230020225207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_4 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (5245862228339 / 6250000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230024216941 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨4, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (5245862228339 / 6250000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230024216941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_5 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83898976530211 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (89201128763 / 4000000000000 : ℝ))
      (E := (cell12879 ⟨5, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83898976530211 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (89201128763 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_6 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (10483022764627 / 12500000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115016119687 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨6, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (10483022764627 / 12500000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115016119687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_7 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83829412378269 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115018113679 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨7, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83829412378269 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115018113679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_8 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (8379466727859 / 10000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557510062057 / 25000000000000 : ℝ))
      (E := (cell12879 ⟨8, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (8379466727859 / 10000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557510062057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_9 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83759946782781 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230044250953 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨9, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83759946782781 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230044250953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_10 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (8372525085583 / 10000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230048242217 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨10, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (8372525085583 / 10000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230048242217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_11 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83690579462907 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115026114229 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨11, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83690579462907 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115026114229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_12 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83655932569361 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446011243173 / 20000000000000 : ℝ))
      (E := (cell12879 ⟨12, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83655932569361 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (446011243173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_13 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (3344852405629 / 4000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (223006026851 / 10000000000000 : ℝ))
      (E := (cell12879 ⟨13, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (3344852405629 / 4000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (223006026851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_14 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83586712142709 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230064275847 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨14, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83586712142709 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230064275847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_15 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (208880346353 / 250000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115034121629 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨15, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (208880346353 / 250000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115034121629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_16 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (10439698662783 / 12500000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230072234081 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨16, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (10439698662783 / 12500000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230072234081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_17 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83483064392141 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230076253281 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨17, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83483064392141 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230076253281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_18 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41724281888623 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230080247331 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨18, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41724281888623 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230080247331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_19 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83414087424167 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557521069729 / 25000000000000 : ℝ))
      (E := (cell12879 ⟨19, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83414087424167 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557521069729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12880_0 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (42036652627209 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114945466493 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨0, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (42036652627209 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114945466493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_1 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (16807677448979 / 20000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (557473729541 / 25000000000000 : ℝ))
      (E := (cell12880 ⟨1, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (16807677448979 / 20000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (557473729541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_2 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (5250218380569 / 6250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229898947507 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨2, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (5250218380569 / 6250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229898947507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_3 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83968625750721 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114951456911 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨3, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83968625750721 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114951456911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_4 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41966891096807 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114953470577 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨4, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41966891096807 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114953470577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_5 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (1048737042273 / 1250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114955460851 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨5, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (1048737042273 / 1250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114955460851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_6 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (16772833855929 / 20000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229914921129 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨6, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (16772833855929 / 20000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229914921129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_7 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83829399851461 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (17421241773 / 781250000000 : ℝ))
      (E := (cell12880 ⟨7, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83829399851461 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (17421241773 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_8 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83794655061907 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (222992294839 / 10000000000000 : ℝ))
      (E := (cell12880 ⟨8, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83794655061907 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (222992294839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_9 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83759934875789 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (5574817331 / 250000000000 : ℝ))
      (E := (cell12880 ⟨9, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83759934875789 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (5574817331 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_10 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41862619629047 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114965481861 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨10, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41862619629047 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114965481861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_11 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (10461321021749 / 12500000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229934932691 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨11, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (10461321021749 / 12500000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229934932691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_12 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (20913980397209 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229938961641 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨12, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (20913980397209 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229938961641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_13 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83621299468157 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (13937143377 / 625000000000 : ℝ))
      (E := (cell12880 ⟨13, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83621299468157 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (13937143377 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_14 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41793350888833 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114973495331 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨14, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41793350888833 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114973495331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_15 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83552128483253 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229951001829 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨15, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83552128483253 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229951001829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_16 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (10439697443873 / 12500000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229954978957 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨16, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (10439697443873 / 12500000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229954978957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_17 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83483054947099 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114979492583 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨17, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83483054947099 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1114979492583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_18 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41724277319007 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (139372685433 / 6250000000000 : ℝ))
      (E := (cell12880 ⟨18, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41724277319007 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (139372685433 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_19 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (1042675982379 / 1250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (89198679477 / 4000000000000 : ℝ))
      (E := (cell12880 ⟨19, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (1042675982379 / 1250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (89198679477 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12881_0 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (42036645273369 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (44595473767 / 2000000000000 : ℝ))
      (E := (cell12881 ⟨0, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (42036645273369 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (44595473767 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_1 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (84038372850379 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229777706947 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨1, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (84038372850379 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229777706947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_2 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (8400348000731 / 10000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114890856299 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨2, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (8400348000731 / 10000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114890856299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_3 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (10496076497651 / 12500000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114892856917 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨3, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (10496076497651 / 12500000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114892856917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_4 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41966884367971 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114894830503 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨4, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41966884367971 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114894830503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_5 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83898950235569 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (17420263109 / 781250000000 : ℝ))
      (E := (cell12881 ⟨5, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83898950235569 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (17420263109 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_6 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (5241509777771 / 6250000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114898857269 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨6, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (5241509777771 / 6250000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114898857269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_7 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83829387326677 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229801720279 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨7, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83829387326677 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229801720279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_8 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83794642847213 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (55745142559 / 2500000000000 : ℝ))
      (E := (cell12881 ⟨8, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83794642847213 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (55745142559 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_9 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20939980742687 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (557452431439 / 25000000000000 : ℝ))
      (E := (cell12881 ⟨9, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20939980742687 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (557452431439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_10 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83725227662271 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278726710137 / 12500000000000 : ℝ))
      (E := (cell12881 ⟨10, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83725227662271 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278726710137 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_11 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41845278443477 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (557454422729 / 25000000000000 : ℝ))
      (E := (cell12881 ⟨11, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41845278443477 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (557454422729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_12 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (1673118212203 / 2000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229821703363 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨12, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (1673118212203 / 2000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229821703363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_13 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83621288797391 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229825724377 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨13, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83621288797391 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229825724377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_14 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (8358669141439 / 10000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229829701497 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨14, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (8358669141439 / 10000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229829701497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_15 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20888029606759 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229833698279 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨15, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20888029606759 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229833698279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_16 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20879392450349 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229837719929 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨16, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20879392450349 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229837719929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_17 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83483045503713 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229841713183 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨17, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83483045503713 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229841713183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_18 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83448545500403 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229845740943 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨18, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83448545500403 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229845740943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_19 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (10426758719757 / 12500000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114924874707 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨19, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (10426758719757 / 12500000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114924874707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12882_0 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (1313644935021 / 1562500000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229656439203 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨0, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (1313644935021 / 1562500000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229656439203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_1 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (328274837727 / 390625000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445932086681 / 20000000000000 : ℝ))
      (E := (cell12882 ⟨1, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (328274837727 / 390625000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445932086681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_2 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (5250216620483 / 6250000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229664473253 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨2, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (5250216620483 / 6250000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229664473253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_3 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83968598213869 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229668451551 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨3, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83968598213869 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229668451551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_4 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41966877640203 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229672492343 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨4, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41966877640203 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229672492343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_5 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83898937091397 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (557419121957 / 25000000000000 : ℝ))
      (E := (cell12882 ⟨5, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83898937091397 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (557419121957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_6 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83864143611089 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (8709689241 / 390625000000 : ℝ))
      (E := (cell12882 ⟨6, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83864143611089 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (8709689241 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_7 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83829374803919 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (278710561171 / 12500000000000 : ℝ))
      (E := (cell12882 ⟨7, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83829374803919 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (278710561171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_8 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41897315317253 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (17837507617 / 800000000000 : ℝ))
      (E := (cell12882 ⟨8, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41897315317253 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (17837507617 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_9 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83759911067657 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114846228453 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨9, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83759911067657 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114846228453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_10 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41862608034181 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445939302093 / 20000000000000 : ℝ))
      (E := (cell12882 ⟨10, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41862608034181 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445939302093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_11 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (326916193757 / 390625000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445940100627 / 20000000000000 : ℝ))
      (E := (cell12882 ⟨11, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (326916193757 / 390625000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445940100627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_12 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83655899633303 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (111485224957 / 5000000000000 : ℝ))
      (E := (cell12882 ⟨12, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83655899633303 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (111485224957 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_13 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20905319532107 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229708504419 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨13, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20905319532107 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229708504419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_14 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83586681052879 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445942504933 / 20000000000000 : ℝ))
      (E := (cell12882 ⟨14, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83586681052879 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445942504933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_15 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83552108372547 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229716507147 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨15, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83552108372547 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229716507147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_16 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83517560053501 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (696787661 / 31250000000 : ℝ))
      (E := (cell12882 ⟨16, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83517560053501 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (696787661 / 31250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_17 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41741518030991 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114862247781 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨17, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41741518030991 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114862247781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_18 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (8344853636441 / 10000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229728511131 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨18, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (8344853636441 / 10000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229728511131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_19 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41707030463687 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114866254057 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨19, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41707030463687 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114866254057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12883_0 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (21018315284559 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229539243373 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨0, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (21018315284559 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229539243373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_1 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (84038344068093 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (445908654219 / 20000000000000 : ℝ))
      (E := (cell12883 ⟨1, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (84038344068093 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (445908654219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_2 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (21000862962589 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (44590945747 / 2000000000000 : ℝ))
      (E := (cell12883 ⟨2, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (21000862962589 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (44590945747 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_3 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83968584448703 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557387810693 / 25000000000000 : ℝ))
      (E := (cell12883 ⟨3, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83968584448703 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557387810693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_4 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41966870913503 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229555261403 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨4, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41966870913503 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229555261403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_5 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83898923949323 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (445911858677 / 20000000000000 : ℝ))
      (E := (cell12883 ⟨5, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83898923949323 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (445911858677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_6 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (327594260859 / 390625000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229563288511 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨6, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (327594260859 / 390625000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229563288511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_7 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (5239335142699 / 6250000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (278695906777 / 12500000000000 : ℝ))
      (E := (cell12883 ⟨7, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (5239335142699 / 6250000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (278695906777 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_8 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41897309211893 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (22295712557 / 1000000000000 : ℝ))
      (E := (cell12883 ⟨8, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41897309211893 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (22295712557 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_9 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (20939974791629 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229575299967 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨9, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (20939974791629 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229575299967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_10 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (16745040895273 / 20000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557394819411 / 25000000000000 : ℝ))
      (E := (cell12883 ⟨10, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (16745040895273 / 20000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557394819411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_11 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83690534318507 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (69674478477 / 3125000000000 : ℝ))
      (E := (cell12883 ⟨11, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83690534318507 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (69674478477 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_12 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (10456986082287 / 12500000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (139349205679 / 6250000000000 : ℝ))
      (E := (cell12883 ⟨12, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (10456986082287 / 12500000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (139349205679 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_13 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41810633730633 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229591280447 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨13, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41810633730633 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229591280447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_14 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83586670693133 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229595285701 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨14, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83586670693133 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229595285701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_15 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83552098319787 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (89183972483 / 4000000000000 : ℝ))
      (E := (cell12883 ⟨15, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83552098319787 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (89183972483 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_16 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83517550307297 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (222960330657 / 10000000000000 : ℝ))
      (E := (cell12883 ⟨16, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83517550307297 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (222960330657 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_17 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83483026621907 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114803666151 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨17, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83483026621907 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114803666151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_18 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (16689705446007 / 20000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114805667871 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨18, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (16689705446007 / 20000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114805667871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_19 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41707026049137 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229615321297 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨19, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41707026049137 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229615321297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12884_0 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (42036623218707 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (1114711050431 / 50000000000000 : ℝ))
      (E := (cell12884 ⟨0, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (42036623218707 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (1114711050431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_1 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (42019164840161 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229426104313 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨1, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (42019164840161 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229426104313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_2 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (16800687555039 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445886019403 / 20000000000000 : ℝ))
      (E := (cell12884 ⟨2, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (16800687555039 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445886019403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_3 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83968570685711 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (278679260937 / 12500000000000 : ℝ))
      (E := (cell12884 ⟨3, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83968570685711 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (278679260937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_4 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83933728375741 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557359521007 / 25000000000000 : ℝ))
      (E := (cell12884 ⟨4, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83933728375741 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557359521007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_5 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (20974727702337 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (69670065457 / 3125000000000 : ℝ))
      (E := (cell12884 ⟨5, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (20974727702337 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (69670065457 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_6 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83864117950779 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229446127047 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨6, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83864117950779 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229446127047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_7 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83829349764473 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229450130807 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨7, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83829349764473 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229450130807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_8 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (20948651553763 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229454113089 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨8, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (20948651553763 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229454113089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_9 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (20939971816831 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229458138863 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨9, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (20939971816831 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229458138863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_10 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83725192886281 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229462098757 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨10, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83725192886281 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229462098757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_11 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (10461315379637 / 12500000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (278683264413 / 12500000000000 : ℝ))
      (E := (cell12884 ⟨11, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (10461315379637 / 12500000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (278683264413 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_12 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41827938842563 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229470136647 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨12, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41827938842563 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229470136647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_13 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83621256795907 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (17417766489 / 781250000000 : ℝ))
      (E := (cell12884 ⟨13, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83621256795907 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (17417766489 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_14 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (5224166270947 / 6250000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (69671192471 / 3125000000000 : ℝ))
      (E := (cell12884 ⟨14, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (5224166270947 / 6250000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (69671192471 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_15 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (16710417653751 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445896422613 / 20000000000000 : ℝ))
      (E := (cell12884 ⟨15, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (16710417653751 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445896422613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_16 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (2609923142587 / 3125000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (1114743076121 / 50000000000000 : ℝ))
      (E := (cell12884 ⟨16, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (2609923142587 / 3125000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (1114743076121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_17 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41741508591743 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229490165179 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨17, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41741508591743 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229490165179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_18 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83448518097279 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229494156527 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨18, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83448518097279 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229494156527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_19 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (16682808654151 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557374532673 / 25000000000000 : ℝ))
      (E := (cell12884 ⟨19, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (16682808654151 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557374532673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12885_0 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (21018307934719 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229304953843 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨0, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (21018307934719 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229304953843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_1 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (84038315294799 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114654466531 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨1, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (84038315294799 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114654466531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_2 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (84003423702243 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557328240031 / 25000000000000 : ℝ))
      (E := (cell12885 ⟨2, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (84003423702243 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557328240031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_3 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (8396855692489 / 10000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557329231957 / 25000000000000 : ℝ))
      (E := (cell12885 ⟨3, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (8396855692489 / 10000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557329231957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_4 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20983428731653 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (111466048011 / 5000000000000 : ℝ))
      (E := (cell12885 ⟨4, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20983428731653 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (111466048011 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_5 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (8389889767147 / 10000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229324949493 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨5, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (8389889767147 / 10000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229324949493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_6 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16772821024743 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (278666120163 / 12500000000000 : ℝ))
      (E := (cell12885 ⟨6, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16772821024743 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (278666120163 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_7 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16765867449557 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114666472583 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨7, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16765867449557 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114666472583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_8 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (5237162125519 / 6250000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557334241569 / 25000000000000 : ℝ))
      (E := (cell12885 ⟨8, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (5237162125519 / 6250000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557334241569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_9 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (83759875370081 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557335243399 / 25000000000000 : ℝ))
      (E := (cell12885 ⟨9, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (83759875370081 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557335243399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_10 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20931295324527 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229344973807 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨10, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20931295324527 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229344973807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_11 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (83690511757561 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (111467448667 / 5000000000000 : ℝ))
      (E := (cell12885 ⟨11, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (83690511757561 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (111467448667 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_12 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16731173342759 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229352978379 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨12, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16731173342759 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229352978379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_13 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20905311533087 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114678497429 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨13, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20905311533087 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114678497429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_14 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16717329995787 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229360970313 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨14, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16717329995787 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229360970313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_15 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (1671041564389 / 2000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114682484149 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨15, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (1671041564389 / 2000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114682484149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_16 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (83517530819963 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114684497007 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨16, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (83517530819963 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114684497007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_17 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (83483007746719 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (445874598839 / 20000000000000 : ℝ))
      (E := (cell12885 ⟨17, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (83483007746719 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (445874598839 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_18 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (4172425448307 / 5000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229377031737 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨18, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (4172425448307 / 5000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229377031737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_19 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (41707017222409 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229380994573 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨19, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (41707017222409 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229380994573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12886_0 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (42036608521311 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229187802317 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨0, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (42036608521311 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229187802317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_1 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (42019150455761 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229191815193 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨1, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (42019150455761 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229191815193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_2 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (84003409631501 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (5572989547 / 250000000000 : ℝ))
      (E := (cell12886 ⟨2, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (84003409631501 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (5572989547 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_3 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83968543166241 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114599910833 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨3, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83968543166241 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114599910833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_4 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83933701479617 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114601916029 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨4, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83933701479617 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114601916029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_5 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83898884535689 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229207857991 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨5, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83898884535689 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229207857991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_6 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83864092298711 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (557302962313 / 25000000000000 : ℝ))
      (E := (cell12886 ⟨6, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83864092298711 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (557302962313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_7 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (261966639791 / 312500000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229215871269 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨7, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (261966639791 / 312500000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229215871269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_8 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41897290901771 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (557304968319 / 25000000000000 : ℝ))
      (E := (cell12886 ⟨8, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41897290901771 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (557304968319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_9 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83759863474787 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229223862203 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨9, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83759863474787 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229223862203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_10 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83725169711847 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229227844731 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨10, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83725169711847 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229227844731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_11 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (836905004799 / 1000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (17833855083 / 800000000000 : ℝ))
      (E := (cell12886 ⟨11, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (836905004799 / 1000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (17833855083 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_12 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41827927872151 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229235874169 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨12, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41827927872151 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229235874169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_13 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83621235470591 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229239875111 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨13, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83621235470591 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229239875111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_14 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83586639624483 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (222924389389 / 10000000000000 : ℝ))
      (E := (cell12886 ⟨14, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83586639624483 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (222924389389 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_15 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83552068171873 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (557311969443 / 25000000000000 : ℝ))
      (E := (cell12886 ⟨15, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83552068171873 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (557311969443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_16 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (5219845067427 / 6250000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229251890089 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨16, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (5219845067427 / 6250000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229251890089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_17 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83482998311607 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114627938787 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨17, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83482998311607 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114627938787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_18 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41724249918309 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229259903123 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨18, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41724249918309 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229259903123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_19 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83414025620461 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229263912939 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨19, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83414025620461 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229263912939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12887_0 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (21018300587163 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229070761941 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨0, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (21018300587163 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229070761941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_1 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (84038286530491 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229074750709 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨1, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (84038286530491 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229074750709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_2 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (84003395562967 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557269682731 / 25000000000000 : ℝ))
      (E := (cell12887 ⟨2, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (84003395562967 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557269682731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_3 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20992132352441 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557270692253 / 25000000000000 : ℝ))
      (E := (cell12887 ⟨3, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20992132352441 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557270692253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_4 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (16786737606951 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229086757467 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨4, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (16786737606951 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229086757467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_5 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (16779774280401 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (89163630487 / 4000000000000 : ℝ))
      (E := (cell12887 ⟨5, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (16779774280401 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (89163630487 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_6 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41932039737883 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557273683231 / 25000000000000 : ℝ))
      (E := (cell12887 ⟨6, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41932039737883 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557273683231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_7 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41914656110239 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229098735141 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨7, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41914656110239 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229098735141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_8 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41897284800383 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (89164111043 / 4000000000000 : ℝ))
      (E := (cell12887 ⟨8, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41897284800383 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (89164111043 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_9 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (83759851581441 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (278638343331 / 12500000000000 : ℝ))
      (E := (cell12887 ⟨9, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (83759851581441 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (278638343331 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_10 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41862579063749 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229110769593 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨10, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41862579063749 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229110769593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_11 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (83690489204113 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557278698331 / 25000000000000 : ℝ))
      (E := (cell12887 ⟨11, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (83690489204113 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557278698331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_12 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41827922388323 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229118765911 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨12, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41827922388323 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229118765911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_13 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (83621224810633 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114561375677 / 50000000000000 : ℝ))
      (E := (cell12887 ⟨13, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (83621224810633 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114561375677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_14 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41793314635897 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229126755339 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨14, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41793314635897 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229126755339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_15 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41776029063011 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (139320673957 / 6250000000000 : ℝ))
      (E := (cell12887 ⟨15, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41776029063011 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (139320673957 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_16 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (83517511339391 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229134782267 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨16, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (83517511339391 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229134782267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_17 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20870747219537 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229138815319 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨17, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20870747219537 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229138815319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_18 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41724245354357 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114571385343 / 50000000000000 : ℝ))
      (E := (cell12887 ⟨18, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41724245354357 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114571385343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_19 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (16682803359537 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229146827521 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨19, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (16682803359537 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229146827521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12888_0 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (42036593828483 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2228953659233 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨0, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (42036593828483 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2228953659233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_1 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (42019136075853 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2228957681759 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨1, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (42019136075853 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2228957681759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_2 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (42001690748321 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (139310106031 / 6250000000000 : ℝ))
      (E := (cell12888 ⟨2, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (42001690748321 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (139310106031 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_3 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83968515655457 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2228965654071 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨3, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83968515655457 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2228965654071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_4 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (20983418648007 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557242419631 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨4, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (20983418648007 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557242419631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_5 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41949429135209 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445794732409 / 20000000000000 : ℝ))
      (E := (cell12888 ⟨5, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41949429135209 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445794732409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_6 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (524150416593 / 625000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557244417573 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨6, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (524150416593 / 625000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557244417573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_7 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83829299709857 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114490855381 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨7, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83829299709857 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114490855381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_8 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83794557399973 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114492837339 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨8, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83794557399973 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114492837339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_9 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41879919845021 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2228989684973 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨9, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41879919845021 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2228989684973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_10 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41862573272529 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114496845167 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨10, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41862573272529 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114496845167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_11 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (418452389651 / 500000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557249424297 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨11, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (418452389651 / 500000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557249424297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_12 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41827916905413 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229001711717 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨12, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41827916905413 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229001711717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_13 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (20905303538119 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229005739853 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨13, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (20905303538119 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229005739853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_14 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (20896654730217 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229009729129 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨14, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (20896654730217 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229009729129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_15 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41776024040949 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229013743097 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨15, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41776024040949 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229013743097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_16 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (2087937540041 / 2500000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (139313608047 / 6250000000000 : ℝ))
      (E := (cell12888 ⟨16, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (2087937540041 / 2500000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (139313608047 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_17 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83482979446341 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229021749207 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨17, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83482979446341 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229021749207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_18 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41724240791213 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229025750927 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨18, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41724240791213 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229025750927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_19 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83414007976489 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229029738319 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨19, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83414007976489 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229029738319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12889_0 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (42036586483781 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (278604576231 / 12500000000000 : ℝ))
      (E := (cell12889 ⟨0, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (42036586483781 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (278604576231 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_1 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (42019128887583 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114420333097 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨1, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (42019128887583 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114420333097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_2 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (21000841858131 / 25000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (55721116441 / 2500000000000 : ℝ))
      (E := (cell12889 ⟨2, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (21000841858131 / 25000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (55721116441 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_3 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83968501903321 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228848650537 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨3, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83968501903321 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228848650537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_4 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83933661151433 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (69651645411 / 3125000000000 : ℝ))
      (E := (cell12889 ⟨4, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83933661151433 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (69651645411 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_5 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (3355953805637 / 4000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (445771334699 / 20000000000000 : ℝ))
      (E := (cell12889 ⟨5, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (3355953805637 / 4000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (445771334699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_6 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83864053836053 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (278607582669 / 12500000000000 : ℝ))
      (E := (cell12889 ⟨6, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83864053836053 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (278607582669 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_7 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83829287201257 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228864682147 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨7, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83829287201257 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228864682147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_8 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (16758909040233 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228868685113 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨8, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (16758909040233 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228868685113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_9 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83759827800591 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (89154907087 / 4000000000000 : ℝ))
      (E := (cell12889 ⟨9, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83759827800591 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (89154907087 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_10 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83725134964529 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228876665013 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨10, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83725134964529 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228876665013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_11 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (1046130833227 / 1250000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228880655053 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨11, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (1046130833227 / 1250000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228880655053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_12 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83655822846843 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114442326737 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨12, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83655822846843 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114442326737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_13 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41810601748059 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (222888866621 / 10000000000000 : ℝ))
      (E := (cell12889 ⟨13, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41810601748059 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (222888866621 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_14 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (16717321714341 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228892698947 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨14, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (16717321714341 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228892698947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_15 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (167104076079 / 200000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228896698947 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨15, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (167104076079 / 200000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228896698947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_16 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41758745932789 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228900671339 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨16, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41758745932789 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228900671339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_17 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (20870742504047 / 25000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114452339617 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨17, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (20870742504047 / 25000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114452339617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_18 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41724236228877 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228908669097 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨18, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41724236228877 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228908669097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_19 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (10426749894609 / 12500000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (445782540721 / 20000000000000 : ℝ))
      (E := (cell12889 ⟨19, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (10426749894609 / 12500000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (445782540721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12890_0 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (2101828957011 / 2500000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (222871961379 / 10000000000000 : ℝ))
      (E := (cell12890 ⟨0, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (2101828957011 / 2500000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (222871961379 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_1 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (8403824340087 / 10000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228723646167 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨1, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (8403824340087 / 10000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228723646167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_2 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (84003353370613 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228727614359 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨2, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (84003353370613 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228727614359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_3 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41984244076677 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228731642617 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨3, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41984244076677 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228731642617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_4 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83933647712971 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228735623431 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨4, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83933647712971 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228735623431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_5 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83898832013529 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228739622687 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨5, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83898832013529 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228739622687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_6 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (20966010254821 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (111437182407 / 5000000000000 : ℝ))
      (E := (cell12890 ⟨6, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (20966010254821 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (111437182407 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_7 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41914637347339 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228747649297 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨7, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41914637347339 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228747649297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_8 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83794533004341 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445750326667 / 20000000000000 : ℝ))
      (E := (cell12890 ⟨8, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83794533004341 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445750326667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_9 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41879907956543 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (111437783261 / 5000000000000 : ℝ))
      (E := (cell12890 ⟨9, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41879907956543 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (111437783261 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_10 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (8372512338591 / 10000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557189908893 / 25000000000000 : ℝ))
      (E := (cell12890 ⟨10, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (8372512338591 / 10000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557189908893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_11 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83690455387993 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228763666921 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨11, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83690455387993 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228763666921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_12 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (16731162376939 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228767649297 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨12, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (16731162376939 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228767649297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_13 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83621192841559 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228771646693 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨13, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83621192841559 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228771646693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_14 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83586598224303 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557193916199 / 25000000000000 : ℝ))
      (E := (cell12890 ⟨14, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83586598224303 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557193916199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_15 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83552027998827 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228779650867 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨15, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83552027998827 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228779650867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_16 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (16703496426241 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557195917059 / 25000000000000 : ℝ))
      (E := (cell12890 ⟨16, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (16703496426241 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557195917059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_17 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83482960587687 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (139299228977 / 6250000000000 : ℝ))
      (E := (cell12890 ⟨17, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83482960587687 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (139299228977 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_18 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83448463334697 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557197924987 / 25000000000000 : ℝ))
      (E := (cell12890 ⟨18, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83448463334697 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (557197924987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_19 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (16682798067767 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (222879566511 / 10000000000000 : ℝ))
      (E := (cell12890 ⟨19, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (16682798067767 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (222879566511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12891_0 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (84073143595599 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (111430133553 / 5000000000000 : ℝ))
      (E := (cell12891 ⟨0, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (84073143595599 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (111430133553 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_1 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (84038229028819 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (89144264867 / 4000000000000 : ℝ))
      (E := (cell12891 ⟨1, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (84038229028819 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (89144264867 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_2 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (84003339310909 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (139288164033 / 6250000000000 : ℝ))
      (E := (cell12891 ⟨2, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (84003339310909 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (139288164033 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_3 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83968474405557 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228614630309 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨3, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83968474405557 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228614630309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_4 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (524585214229 / 625000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (445723729457 / 20000000000000 : ℝ))
      (E := (cell12891 ⟨4, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (524585214229 / 625000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (445723729457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_5 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41949409444113 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228622683463 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨5, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41949409444113 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228622683463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_6 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (20966007051143 / 25000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1088196597 / 48828125000 : ℝ))
      (E := (cell12891 ⟨6, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (20966007051143 / 25000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1088196597 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_7 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (2095731554753 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (445726134041 / 20000000000000 : ℝ))
      (E := (cell12891 ⟨7, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (2095731554753 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (445726134041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_8 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (167589041619 / 200000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228634693393 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨8, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (167589041619 / 200000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228634693393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_9 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83759804027527 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114319324553 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨9, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83759804027527 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114319324553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_10 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (209312779523 / 250000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114321330037 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨10, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (209312779523 / 250000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114321330037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_11 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83690444119697 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (557161668677 / 25000000000000 : ℝ))
      (E := (cell12891 ⟨11, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83690444119697 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (557161668677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_12 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83655800924383 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (139290668699 / 6250000000000 : ℝ))
      (E := (cell12891 ⟨12, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83655800924383 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (139290668699 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_13 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41810591094399 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114327340651 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨13, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41810591094399 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114327340651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_14 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (10448323484833 / 12500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (69645583901 / 3125000000000 : ℝ))
      (E := (cell12891 ⟨14, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (10448323484833 / 12500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (69645583901 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_15 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (2088800448997 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114331357607 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨15, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (2088800448997 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114331357607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_16 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (2087936809963 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114333359721 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨16, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (2087936809963 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114333359721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_17 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83482951160837 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1392919189 / 62500000000 : ℝ))
      (E := (cell12891 ⟨17, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83482951160837 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1392919189 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_18 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (10431056776657 / 12500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (111433736349 / 5000000000000 : ℝ))
      (E := (cell12891 ⟨18, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (10431056776657 / 12500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (111433736349 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_19 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (10426747690297 / 12500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114339340553 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨19, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (10426747690297 / 12500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114339340553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12892_0 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (1050914111413 / 1250000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114242833 / 50000000000 : ℝ))
      (E := (cell12892 ⟨0, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (1050914111413 / 1250000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114242833 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_1 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (84038214659011 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228489708427 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨1, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (84038214659011 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228489708427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_2 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (84003325253411 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228493688149 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨2, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (84003325253411 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228493688149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_3 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83968460659929 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (445699534303 / 20000000000000 : ℝ))
      (E := (cell12892 ⟨3, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83968460659929 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (445699534303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_4 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83933620842441 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114250862357 / 50000000000000 : ℝ))
      (E := (cell12892 ⟨4, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83933620842441 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114250862357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_5 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41949402882509 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114252840991 / 50000000000000 : ℝ))
      (E := (cell12892 ⟨5, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41949402882509 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114252840991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_6 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83864015391917 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (55712743121 / 2500000000000 : ℝ))
      (E := (cell12892 ⟨6, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83864015391917 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (55712743121 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_7 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83829249687581 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228513686881 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨7, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83829249687581 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228513686881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_8 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41897254308321 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (55712942281 / 2500000000000 : ℝ))
      (E := (cell12892 ⟨8, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41897254308321 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (55712942281 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_9 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41879896071957 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (3565634699 / 160000000000 : ℝ))
      (E := (cell12892 ⟨9, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41879896071957 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (3565634699 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_10 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41862550117199 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (55713143463 / 2500000000000 : ℝ))
      (E := (cell12892 ⟨10, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41862550117199 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (55713143463 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_11 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41845216426637 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228529736499 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨11, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41845216426637 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228529736499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_12 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41827894982953 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557133436257 / 25000000000000 : ℝ))
      (E := (cell12892 ⟨12, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41827894982953 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557133436257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_13 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (20905292884459 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (445707542381 / 20000000000000 : ℝ))
      (E := (cell12892 ⟨13, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (20905292884459 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (445707542381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_14 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41793288767393 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (22285417009 / 1000000000000 : ℝ))
      (E := (cell12892 ⟨14, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41793288767393 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (22285417009 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_15 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83552007922657 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228545717451 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨15, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83552007922657 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228545717451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_16 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (20879365666881 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (278568713569 / 12500000000000 : ℝ))
      (E := (cell12892 ⟨16, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (20879365666881 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (278568713569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_17 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83482941735639 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (69642304291 / 3125000000000 : ℝ))
      (E := (cell12892 ⟨17, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83482941735639 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (69642304291 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_18 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (8344844509343 / 10000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228557750193 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨18, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (8344844509343 / 10000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228557750193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_19 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (10426746588437 / 12500000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (445712350319 / 20000000000000 : ℝ))
      (E := (cell12892 ⟨19, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (10426746588437 / 12500000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (445712350319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12893_0 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (84073114232761 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228368772099 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨0, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (84073114232761 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228368772099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_1 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (42019100145723 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114186366433 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨1, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (42019100145723 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114186366433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_2 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (84003311198119 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (557094186837 / 25000000000000 : ℝ))
      (E := (cell12893 ⟨2, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (84003311198119 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (557094186837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_3 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (20992111729117 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114190383119 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨3, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (20992111729117 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114190383119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_4 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83933607410373 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114192369937 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨4, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83933607410373 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114192369937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_5 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (1310918635061 / 1562500000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114194396043 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨5, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (1310918635061 / 1562500000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114194396043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_6 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41932001290659 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114196378393 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨6, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41932001290659 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114196378393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_7 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41914618593531 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114198378659 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨7, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41914618593531 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114198378659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_8 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41897248212883 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228400800927 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨8, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41897248212883 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228400800927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_9 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83759780262247 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228404778527 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨9, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83759780262247 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228404778527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_10 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (16745017732301 / 20000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445681750957 / 20000000000000 : ℝ))
      (E := (cell12893 ⟨10, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (16745017732301 / 20000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445681750957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_11 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41845210794361 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228412794211 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨11, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41845210794361 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228412794211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_12 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83655779009263 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228416786831 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨12, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83655779009263 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228416786831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_13 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83621160888671 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114210398319 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨13, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83621160888671 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114210398319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_14 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83586567192669 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114212385579 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨14, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83586567192669 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114212385579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_15 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41775998943579 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228428773939 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨15, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41775998943579 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228428773939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_16 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (16703490587643 / 20000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228432810177 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨16, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (16703490587643 / 20000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228432810177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_17 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (20870733078023 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114218413299 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨17, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (20870733078023 / 25000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114218413299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_18 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41724217987609 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228440827841 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨18, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41724217987609 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228440827841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_19 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83413963894193 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228444818307 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨19, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83413963894193 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228444818307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12894_0 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (42036549777381 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (22282518737 / 1000000000000 : ℝ))
      (E := (cell12894 ⟨0, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (42036549777381 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (22282518737 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_1 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (21009546481531 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228255868549 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨1, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (21009546481531 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228255868549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_2 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (10500412143129 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228259860001 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨2, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (10500412143129 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228259860001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_3 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (10496054146897 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (89130554263 / 4000000000000 : ℝ))
      (E := (cell12894 ⟨3, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (10496054146897 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (89130554263 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_4 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20983398495109 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114133933267 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨4, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20983398495109 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114133933267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_5 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83898779524883 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (34816747499 / 1562500000000 : ℝ))
      (E := (cell12894 ⟨5, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83898779524883 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (34816747499 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_6 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (10482998721597 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228275842431 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨6, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (10482998721597 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228275842431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_7 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83829224688561 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228279881517 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨7, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83829224688561 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228279881517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_8 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83794484236871 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (557070962101 / 25000000000000 : ℝ))
      (E := (cell12894 ⟨8, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83794484236871 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (557070962101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_9 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20939942095631 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (89131514641 / 4000000000000 : ℝ))
      (E := (cell12894 ⟨9, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20939942095631 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (89131514641 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_10 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83725077090519 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228291883059 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨10, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83725077090519 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228291883059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_11 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83690410326041 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (222829590593 / 10000000000000 : ℝ))
      (E := (cell12894 ⟨11, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83690410326041 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (222829590593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_12 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (16731153610891 / 20000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (22282998827 / 1000000000000 : ℝ))
      (E := (cell12894 ⟨12, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (16731153610891 / 20000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (22282998827 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_13 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (10452643780163 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445660775473 / 20000000000000 : ℝ))
      (E := (cell12894 ⟨13, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (10452643780163 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445660775473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_14 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83586556852313 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445661579121 / 20000000000000 : ℝ))
      (E := (cell12894 ⟨14, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83586556852313 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445661579121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_15 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83551987853383 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114155942339 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨15, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83551987853383 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114155942339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_16 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83517443210593 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228315907911 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨16, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83517443210593 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228315907911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_17 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20870730722549 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228319912029 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨17, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20870730722549 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228319912029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_18 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83448426858621 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228323901671 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨18, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83448426858621 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228323901671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_19 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83413955082469 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228327939511 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨19, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83413955082469 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228327939511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12895_0 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (84073084879043 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228134970803 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨0, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (84073084879043 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228134970803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_1 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (21009542890761 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228138999773 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨1, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (21009542890761 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228138999773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_2 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (1680065661883 / 2000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228142968233 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨2, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (1680065661883 / 2000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228142968233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_3 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (1679368388721 / 2000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (139259187527 / 6250000000000 : ℝ))
      (E := (cell12895 ⟨3, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (1679368388721 / 2000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (139259187527 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_4 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20983395138157 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228150988851 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨4, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20983395138157 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228150988851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_5 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41949383203977 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114077499687 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨5, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41949383203977 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114077499687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_6 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83863976966289 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228158981779 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨6, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83863976966289 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228158981779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_7 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83829212192079 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228163001487 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨7, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83829212192079 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228163001487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_8 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41897236024979 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228167007723 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨8, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41897236024979 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228167007723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_9 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (16751951300949 / 20000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228171007409 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨9, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (16751951300949 / 20000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228171007409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_10 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83725065521441 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114087503609 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨10, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83725065521441 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114087503609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_11 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83690399065231 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222817901357 / 10000000000000 : ℝ))
      (E := (cell12895 ⟨11, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83690399065231 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222817901357 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_12 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (2091393927537 / 2500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228183032641 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨12, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (2091393927537 / 2500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228183032641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_13 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83621139595733 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (89127480489 / 4000000000000 : ℝ))
      (E := (cell12895 ⟨13, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83621139595733 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (89127480489 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_14 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20896636628429 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228191016089 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨14, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20896636628429 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228191016089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_15 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20887994455333 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222819499149 / 10000000000000 : ℝ))
      (E := (cell12895 ⟨15, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20887994455333 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222819499149 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_16 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41758716742329 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (445639800351 / 20000000000000 : ℝ))
      (E := (cell12895 ⟨16, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41758716742329 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (445639800351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_17 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (1669658269399 / 2000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (445640610367 / 20000000000000 : ℝ))
      (E := (cell12895 ⟨17, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (1669658269399 / 2000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (445640610367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_18 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83448417743637 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228207029937 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨18, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83448417743637 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228207029937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_19 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83413946272321 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228211056939 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨19, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83413946272321 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228211056939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12896_0 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (42036535102801 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228018121241 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨0, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (42036535102801 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228018121241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_1 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (16807631440441 / 20000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228022126541 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨1, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (16807631440441 / 20000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228022126541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_2 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (84003269045471 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557006532481 / 25000000000000 : ℝ))
      (E := (cell12896 ⟨2, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (84003269045471 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557006532481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_3 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (20992101424773 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114015069953 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨3, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (20992101424773 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114015069953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_4 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (1678671342539 / 2000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (89121364273 / 4000000000000 : ℝ))
      (E := (cell12896 ⟨4, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (1678671342539 / 2000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (89121364273 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_5 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41949376646559 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228038154507 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨5, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41949376646559 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228038154507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_6 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83863964161857 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (111402105843 / 5000000000000 : ℝ))
      (E := (cell12896 ⟨6, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83863964161857 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (111402105843 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_7 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (16765839939523 / 20000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557011529307 / 25000000000000 : ℝ))
      (E := (cell12896 ⟨7, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (16765839939523 / 20000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557011529307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_8 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41897229932513 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228050162851 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨8, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41897229932513 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228050162851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_9 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (8375974462891 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228054144641 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨9, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (8375974462891 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228054144641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_10 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (8372505395427 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114029063631 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨10, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (8372505395427 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114029063631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_11 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (8369038780629 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228062175221 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨11, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (8369038780629 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228062175221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_12 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41827873075169 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114033089271 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨12, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41827873075169 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114033089271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_13 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83621128951959 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228070143083 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨13, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83621128951959 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228070143083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_14 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (1044831702211 / 1250000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445614838153 / 20000000000000 : ℝ))
      (E := (cell12896 ⟨14, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (1044831702211 / 1250000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445614838153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_15 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83551967791003 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557019538139 / 25000000000000 : ℝ))
      (E := (cell12896 ⟨15, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83551967791003 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (557019538139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_16 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83517423760409 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445616429983 / 20000000000000 : ℝ))
      (E := (cell12896 ⟨16, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83517423760409 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445616429983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_17 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41741452025677 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (222808618779 / 10000000000000 : ℝ))
      (E := (cell12896 ⟨17, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41741452025677 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (222808618779 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_18 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41724204315133 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228090154391 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨18, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41724204315133 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228090154391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_19 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83413937463751 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (222809417059 / 10000000000000 : ℝ))
      (E := (cell12896 ⟨19, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83413937463751 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (222809417059 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12897_0 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (2101826388361 / 2500000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1113950633591 / 50000000000000 : ℝ))
      (E := (cell12897 ⟨0, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (2101826388361 / 2500000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1113950633591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_1 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (84038142843607 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445581061341 / 20000000000000 : ℝ))
      (E := (cell12897 ⟨1, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (84038142843607 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445581061341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_2 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (21000813749749 / 25000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445581857439 / 20000000000000 : ℝ))
      (E := (cell12897 ⟨2, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (21000813749749 / 25000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445581857439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_3 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (839683919643 / 1000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (89116531 / 4000000000 : ℝ))
      (E := (cell12897 ⟨3, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (839683919643 / 1000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (89116531 / 4000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_4 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83933553703401 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (111395863919 / 5000000000000 : ℝ))
      (E := (cell12897 ⟨4, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83933553703401 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (111395863919 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_5 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83898740180373 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (278490163167 / 12500000000000 : ℝ))
      (E := (cell12897 ⟨5, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83898740180373 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (278490163167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_6 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83863951359479 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1113962652823 / 50000000000000 : ℝ))
      (E := (cell12897 ⟨6, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83863951359479 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1113962652823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_7 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (5239324200323 / 6250000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445585857347 / 20000000000000 : ℝ))
      (E := (cell12897 ⟨7, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (5239324200323 / 6250000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445585857347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_8 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (3351777907283 / 4000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227933313789 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨8, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (3351777907283 / 4000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227933313789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_9 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83759732755019 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227937335761 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨9, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83759732755019 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227937335761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_10 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (16745008477801 / 20000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445588260251 / 20000000000000 : ℝ))
      (E := (cell12897 ⟨10, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (16745008477801 / 20000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445588260251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_11 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83690376549219 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (556986333199 / 25000000000000 : ℝ))
      (E := (cell12897 ⟨11, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83690376549219 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (556986333199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_12 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83655735201029 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445589864081 / 20000000000000 : ℝ))
      (E := (cell12897 ⟨12, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83655735201029 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445589864081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_13 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83621118309981 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227953328073 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨13, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83621118309981 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227953328073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_14 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41793262920901 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227957361479 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨14, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41793262920901 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227957361479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_15 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83551957762397 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227961367877 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨15, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83551957762397 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227961367877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_16 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83517414037847 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227965352389 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨16, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83517414037847 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227965352389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_17 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83482894634407 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227969378121 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨17, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83482894634407 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227969378121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_18 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83448399518509 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (13924833333 / 625000000000 : ℝ))
      (E := (cell12897 ⟨18, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83448399518509 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (13924833333 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_19 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83413928656757 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227977338739 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨19, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83413928656757 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227977338739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12898_0 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (21018260216389 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (111389223323 / 5000000000000 : ℝ))
      (E := (cell12898 ⟨0, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (21018260216389 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (111389223323 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_1 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (336152513949 / 400000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556947120603 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨1, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (336152513949 / 400000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556947120603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_2 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (21000810238681 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113896248963 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨2, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (21000810238681 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113896248963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_3 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83968378231673 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556949130379 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨3, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83968378231673 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556949130379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_4 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (4196677014099 / 5000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113900251759 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨4, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (4196677014099 / 5000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113900251759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_5 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (2097468176743 / 2500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227804509809 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨5, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (2097468176743 / 2500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227804509809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_6 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (20965984639789 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227808490167 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨6, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (20965984639789 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227808490167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_7 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41914587357369 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (278476563751 / 12500000000000 : ℝ))
      (E := (cell12898 ⟨7, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41914587357369 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (278476563751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_8 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83794435501103 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556954129639 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨8, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83794435501103 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556954129639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_9 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83759720883071 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (222782052273 / 10000000000000 : ℝ))
      (E := (cell12898 ⟨9, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83759720883071 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (222782052273 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_10 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83725030825647 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113912264599 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨10, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83725030825647 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113912264599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_11 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83690365294017 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113914272191 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨11, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83690365294017 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113914272191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_12 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (5228482765847 / 6250000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227832516341 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨12, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (5228482765847 / 6250000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227832516341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_13 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41810553834899 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (278479563633 / 12500000000000 : ℝ))
      (E := (cell12898 ⟨13, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41810553834899 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (278479563633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_14 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (20896628877121 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (222784052823 / 10000000000000 : ℝ))
      (E := (cell12898 ⟨14, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (20896628877121 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (222784052823 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_15 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83551947735513 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113922260547 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨15, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83551947735513 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113922260547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_16 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83517404316969 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113924275489 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨16, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83517404316969 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113924275489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_17 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83482885219109 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556963141151 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨17, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83482885219109 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556963141151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_18 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (20862097602091 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (139241035413 / 6250000000000 : ℝ))
      (E := (cell12898 ⟨18, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (20862097602091 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (139241035413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_19 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41706959925669 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556965140347 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨19, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41706959925669 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556965140347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12899_0 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (84073026198949 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556916929769 / 25000000000000 : ℝ))
      (E := (cell12899 ⟨0, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (84073026198949 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556916929769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_1 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (84038114133133 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227671711519 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨1, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (84038114133133 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227671711519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_2 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (16800645382531 / 20000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227675704241 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨2, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (16800645382531 / 20000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227675704241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_3 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83968364501211 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445535941151 / 20000000000000 : ℝ))
      (E := (cell12899 ⟨3, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83968364501211 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445535941151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_4 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83933526862687 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227683724317 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨4, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83933526862687 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227683724317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_5 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83898713961157 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113843854991 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨5, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83898713961157 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113843854991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_6 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41931962880443 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556922932099 / 25000000000000 : ℝ))
      (E := (cell12899 ⟨6, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41931962880443 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556922932099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_7 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (3353166489053 / 4000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227695729057 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨7, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (3353166489053 / 4000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227695729057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_8 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83794423322111 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (69615616223 / 3125000000000 : ℝ))
      (E := (cell12899 ⟨8, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83794423322111 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (69615616223 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_9 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (16751941802613 / 20000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (222770376359 / 10000000000000 : ℝ))
      (E := (cell12899 ⟨9, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (16751941802613 / 20000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (222770376359 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_10 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83725019264193 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (278463469129 / 12500000000000 : ℝ))
      (E := (cell12899 ⟨10, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83725019264193 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (278463469129 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_11 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (20922588510171 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (278463968987 / 12500000000000 : ℝ))
      (E := (cell12899 ⟨11, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (20922588510171 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (278463968987 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_12 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83655713307907 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (139232235397 / 6250000000000 : ℝ))
      (E := (cell12899 ⟨12, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83655713307907 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (139232235397 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_13 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (8362109703141 / 10000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (34808121003 / 1562500000000 : ℝ))
      (E := (cell12899 ⟨13, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (8362109703141 / 10000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (34808121003 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_14 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83586505176923 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227723749179 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨14, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83586505176923 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227723749179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_15 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83551937710351 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556931946687 / 25000000000000 : ℝ))
      (E := (cell12899 ⟨15, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83551937710351 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556931946687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_16 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83517394597777 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445546360777 / 20000000000000 : ℝ))
      (E := (cell12899 ⟨16, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83517394597777 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445546360777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_17 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (4174143790273 / 5000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445547161093 / 20000000000000 : ℝ))
      (E := (cell12899 ⟨17, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (4174143790273 / 5000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445547161093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_18 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83448381299831 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113869898063 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨18, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83448381299831 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113869898063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_19 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (10426738880937 / 12500000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227743780263 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨19, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (10426738880937 / 12500000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227743780263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

end BstLean.Part268
