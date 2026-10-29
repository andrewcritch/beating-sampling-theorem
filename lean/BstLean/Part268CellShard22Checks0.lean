import BstLean.Part268CellShard22Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12900_0 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (84073011534619 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227550967199 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨0, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (84073011534619 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227550967199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_1 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (42019049890627 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227554994027 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨1, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (42019049890627 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227554994027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_2 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (21000803218197 / 25000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227558964017 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨2, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (21000803218197 / 25000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227558964017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_3 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (16793670154583 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445512600283 / 20000000000000 : ℝ))
      (E := (cell12900 ⟨3, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (16793670154583 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445512600283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_4 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41966756722761 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227566998699 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨4, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41966756722761 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227566998699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_5 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (16779740170937 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (11137854819 / 500000000000 : ℝ))
      (E := (cell12900 ⟨5, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (16779740170937 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (11137854819 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_6 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (8386391296467 / 10000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227575020331 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨6, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (8386391296467 / 10000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227575020331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_7 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (10478643717491 / 12500000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113789500937 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨7, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (10478643717491 / 12500000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113789500937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_8 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83794411145097 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113791486773 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨8, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83794411145097 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113791486773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_9 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83759697145001 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113793500151 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨9, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83759697145001 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113793500151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_10 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (16745001540929 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113795515409 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨10, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (16745001540929 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113795515409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_11 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83690342789219 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113797506711 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨11, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83690342789219 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113797506711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_12 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83655702364093 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227599012327 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨12, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83655702364093 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227599012327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_13 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41810543197409 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227603033453 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨13, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41810543197409 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227603033453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_14 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83586494847121 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (556901756081 / 25000000000000 : ℝ))
      (E := (cell12900 ⟨14, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83586494847121 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (556901756081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_15 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83551927686911 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227611048479 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨15, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83551927686911 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227611048479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_16 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (8351738488027 / 10000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113807526453 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨16, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (8351738488027 / 10000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113807526453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_17 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41741433196729 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (27845238031 / 1250000000000 : ℝ))
      (E := (cell12900 ⟨17, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41741433196729 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (27845238031 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_18 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83448372192909 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445524604367 / 20000000000000 : ℝ))
      (E := (cell12900 ⟨18, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83448372192909 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445524604367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_19 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83413902245229 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (55690676341 / 2500000000000 : ℝ))
      (E := (cell12900 ⟨19, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83413902245229 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (55690676341 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12901_0 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (16814599374513 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113717134331 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨0, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (16814599374513 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113717134331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_1 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (16807617086323 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113719136041 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨1, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (16807617086323 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113719136041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_2 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (42001599417561 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227442277257 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨2, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (42001599417561 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227442277257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_3 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41984168523391 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227446234801 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨3, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41984168523391 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227446234801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_4 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83933500030483 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113725134373 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨4, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83933500030483 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113725134373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_5 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83898687750303 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445490854253 / 20000000000000 : ℝ))
      (E := (cell12901 ⟨5, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83898687750303 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445490854253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_6 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41931950085253 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445491650007 / 20000000000000 : ℝ))
      (E := (cell12901 ⟨6, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41931950085253 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445491650007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_7 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41914568627773 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227462270469 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨7, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41914568627773 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227462270469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_8 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41897199485031 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556866570447 / 25000000000000 : ℝ))
      (E := (cell12901 ⟨8, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41897199485031 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556866570447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_9 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41879842639439 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556867572727 / 25000000000000 : ℝ))
      (E := (cell12901 ⟨9, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41879842639439 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556867572727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_10 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41862498073501 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113737152247 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨10, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41862498073501 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113737152247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_11 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41845165769811 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113739135439 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨11, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41845165769811 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113739135439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_12 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83655691422111 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113741156189 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨12, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83655691422111 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113741156189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_13 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83621075760019 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (3480447373 / 156250000000 : ℝ))
      (E := (cell12901 ⟨13, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83621075760019 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (3480447373 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_14 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (20896621129769 / 25000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227490295511 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨14, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (20896621129769 / 25000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227490295511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_15 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83551917665191 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (222749430629 / 10000000000000 : ℝ))
      (E := (cell12901 ⟨15, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83551917665191 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (222749430629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_16 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83517375164447 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556874574511 / 25000000000000 : ℝ))
      (E := (cell12901 ⟨16, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83517375164447 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556874574511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_17 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (16696571396621 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (17820018671 / 800000000000 : ℝ))
      (E := (cell12901 ⟨17, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (16696571396621 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (17820018671 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_18 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83448363087599 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445501260397 / 20000000000000 : ℝ))
      (E := (cell12901 ⟨18, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83448363087599 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445501260397 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_19 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83413893444537 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445502064649 / 20000000000000 : ℝ))
      (E := (cell12901 ⟨19, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83413893444537 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445502064649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12902_0 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (84072982212787 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445463513127 / 20000000000000 : ℝ))
      (E := (cell12902 ⟨0, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (84072982212787 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445463513127 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_1 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (42019035542107 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445464309137 / 20000000000000 : ℝ))
      (E := (cell12902 ⟨1, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (42019035542107 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445464309137 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_2 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (84003184799657 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556831396521 / 25000000000000 : ℝ))
      (E := (cell12902 ⟨2, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (84003184799657 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556831396521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_3 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83968323322813 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227329579613 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨3, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83968323322813 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227329579613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_4 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83933486617571 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227333592379 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨4, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83933486617571 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227333592379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_5 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83898674648009 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227337574433 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨5, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83898674648009 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227337574433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_6 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41931943689197 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (111367079571 / 5000000000000 : ℝ))
      (E := (cell12902 ⟨6, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41931943689197 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (111367079571 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_7 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83829124773179 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445469118567 / 20000000000000 : ℝ))
      (E := (cell12902 ⟨7, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83829124773179 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445469118567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_8 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41897193398503 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556837396461 / 25000000000000 : ℝ))
      (E := (cell12902 ⟨8, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41897193398503 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556837396461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_9 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83759673414697 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445470715473 / 20000000000000 : ℝ))
      (E := (cell12902 ⟨9, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83759673414697 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445470715473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_10 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41862492295631 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227357574061 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨10, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41862492295631 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227357574061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_11 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (20922580072973 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227361582349 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨11, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (20922580072973 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227361582349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_12 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83655680481959 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556841402099 / 25000000000000 : ℝ))
      (E := (cell12902 ⟨12, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83655680481959 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556841402099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_13 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41810532563507 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227369599991 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨13, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41810532563507 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227369599991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_14 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (20896618548197 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227373620897 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨14, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (20896618548197 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227373620897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_15 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83551907645191 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113688809181 / 50000000000000 : ℝ))
      (E := (cell12902 ⟨15, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83551907645191 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113688809181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_16 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (20879341362577 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227381597503 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨16, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (20879341362577 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227381597503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_17 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83482847574399 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (139211601339 / 6250000000000 : ℝ))
      (E := (cell12902 ⟨17, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83482847574399 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (139211601339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_18 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (834483539839 / 1000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227389636577 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨18, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (834483539839 / 1000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227389636577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_19 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83413884645419 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227393647353 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨19, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83413884645419 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227393647353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12903_0 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (21018241888821 / 25000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (139200057247 / 6250000000000 : ℝ))
      (E := (cell12903 ⟨0, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (21018241888821 / 25000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (139200057247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_1 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (84038056739051 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227204872693 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨1, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (84038056739051 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227204872693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_2 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (84003170766393 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227208890499 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨2, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (84003170766393 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227208890499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_3 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (5248019350063 / 6250000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (44544258401 / 2000000000000 : ℝ))
      (E := (cell12903 ⟨3, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (5248019350063 / 6250000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (44544258401 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_4 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (16786694641357 / 20000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227216911677 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨4, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (16786694641357 / 20000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227216911677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_5 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (16779732309561 / 20000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227220931251 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨5, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (16779732309561 / 20000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227220931251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_6 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41931937294167 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113612464273 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨6, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41931937294167 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113612464273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_7 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83829112292827 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (111361445549 / 5000000000000 : ℝ))
      (E := (cell12903 ⟨7, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83829112292827 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (111361445549 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_8 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41897187312963 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227232943737 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨8, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41897187312963 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227232943737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_9 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (10469957694057 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227236917719 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨9, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (10469957694057 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227236917719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_10 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83724973037427 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (445448179517 / 20000000000000 : ℝ))
      (E := (cell12903 ⟨10, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83724973037427 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (445448179517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_11 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83690309046029 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227244947839 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨11, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83690309046029 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227244947839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_12 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83655669543637 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113624479247 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨12, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83655669543637 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113624479247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_13 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41810527247901 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227252935403 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨13, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41810527247901 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227252935403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_14 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83586463868257 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113628471163 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨14, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83586463868257 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113628471163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_15 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (2610996800841 / 3125000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227260926513 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨15, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (2610996800841 / 3125000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227260926513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_16 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (20879338934463 / 25000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (445452990257 / 20000000000000 : ℝ))
      (E := (cell12903 ⟨16, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (20879338934463 / 25000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (445452990257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_17 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (4174141908367 / 5000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227268963357 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨17, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (4174141908367 / 5000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227268963357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_18 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83448344881811 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227272967363 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨18, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83448344881811 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227272967363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_19 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (667311006783 / 800000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227276967693 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨19, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (667311006783 / 800000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227276967693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12904_0 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (10509119112507 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227084261779 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨0, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (10509119112507 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227084261779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_1 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (672304339169 / 800000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445417650621 / 20000000000000 : ℝ))
      (E := (cell12904 ⟨1, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (672304339169 / 800000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445417650621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_2 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (2625098647979 / 3125000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227092248381 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨2, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (2625098647979 / 3125000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227092248381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_3 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20992073970341 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556774064029 / 25000000000000 : ℝ))
      (E := (cell12904 ⟨3, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20992073970341 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556774064029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_4 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20983364949531 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556775071141 / 25000000000000 : ℝ))
      (E := (cell12904 ⟨4, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20983364949531 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556775071141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_5 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (10487331056211 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556776070943 / 25000000000000 : ℝ))
      (E := (cell12904 ⟨5, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (10487331056211 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556776070943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_6 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (3354554472013 / 4000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227108261413 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨6, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (3354554472013 / 4000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227108261413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_7 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83829099814489 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227112282899 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨7, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83829099814489 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227112282899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_8 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (10474295307103 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113558148723 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨8, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (10474295307103 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113558148723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_9 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20939912423039 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227120253927 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨9, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20939912423039 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227120253927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_10 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (41862480742747 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227124275067 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨10, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (41862480742747 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227124275067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_11 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83690297802033 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113564154629 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨11, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83690297802033 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113564154629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_12 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (10456957325893 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (27839153807 / 1250000000000 : ℝ))
      (E := (cell12904 ⟨12, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (10456957325893 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (27839153807 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_13 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83621043866383 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (111356813341 / 5000000000000 : ℝ))
      (E := (cell12904 ⟨13, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83621043866383 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (111356813341 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_14 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83586453545483 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556785079489 / 25000000000000 : ℝ))
      (E := (cell12904 ⟨14, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83586453545483 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556785079489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_15 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (5221992975647 / 6250000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227144288927 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨15, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (5221992975647 / 6250000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227144288927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_16 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (2087933650677 / 2500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445429660237 / 20000000000000 : ℝ))
      (E := (cell12904 ⟨16, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (2087933650677 / 2500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445429660237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_17 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (10435353595241 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113576150723 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨17, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (10435353595241 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113576150723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_18 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83448335781333 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227156294341 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨18, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83448335781333 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227156294341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_19 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (16682773410381 / 20000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227160342537 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨19, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (16682773410381 / 20000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227160342537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12905_0 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (42036469123551 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2226967660953 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨0, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (42036469123551 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2226967660953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_1 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (21009507013859 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (222697162907 / 10000000000000 : ℝ))
      (E := (cell12905 ⟨1, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (21009507013859 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (222697162907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_2 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (84003142706463 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2226975659731 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨2, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (84003142706463 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2226975659731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_3 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (20992070540971 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2226979645711 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨3, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (20992070540971 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2226979645711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_4 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83933446391589 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113491826559 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨4, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83933446391589 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113491826559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_5 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (4194931767683 / 5000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2226987631999 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨5, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (4194931767683 / 5000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2226987631999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_6 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41931924507183 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445398329599 / 20000000000000 : ℝ))
      (E := (cell12905 ⟨6, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41931924507183 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445398329599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_7 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (16765817467633 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113497825299 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨7, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (16765817467633 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113497825299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_8 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83794350289699 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113499823487 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨8, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83794350289699 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113499823487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_9 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (16751927566759 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445400728807 / 20000000000000 : ℝ))
      (E := (cell12905 ⟨9, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (16751927566759 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445400728807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_10 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (16744989987093 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227007648443 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨10, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (16744989987093 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227007648443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_11 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41845143279951 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556752916653 / 25000000000000 : ℝ))
      (E := (cell12905 ⟨11, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41845143279951 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556752916653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_12 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83655647672481 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556753911649 / 25000000000000 : ℝ))
      (E := (cell12905 ⟨12, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83655647672481 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556753911649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_13 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83621033238757 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227019652379 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨13, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83621033238757 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227019652379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_14 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (5224152701529 / 6250000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227023689633 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨14, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (5224152701529 / 6250000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227023689633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_15 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (10443984699439 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445405541121 / 20000000000000 : ℝ))
      (E := (cell12905 ⟨15, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (10443984699439 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445405541121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_16 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (8351733631799 / 10000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227031705411 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨16, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (8351733631799 / 10000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227031705411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_17 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83482819358161 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113517846961 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨17, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83482819358161 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113517846961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_18 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (2607760208827 / 3125000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227039675767 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨18, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (2607760208827 / 3125000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227039675767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_19 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83413858257509 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227043713613 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨19, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83413858257509 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227043713613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12906_0 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (42036461798211 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226851055641 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨0, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (42036461798211 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226851055641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_1 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (84038013716983 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226855058443 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨1, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (84038013716983 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226855058443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_2 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (84003128679797 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (139178691667 / 6250000000000 : ℝ))
      (E := (cell12906 ⟨2, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (84003128679797 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (139178691667 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_3 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (20992067112141 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226863030937 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨3, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (20992067112141 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226863030937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_4 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83933432987177 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445373415053 / 20000000000000 : ℝ))
      (E := (cell12906 ⟨4, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83933432987177 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445373415053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_5 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41949311129859 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (55671775847 / 2500000000000 : ℝ))
      (E := (cell12906 ⟨5, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41949311129859 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (55671775847 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_6 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41931918115229 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226875088291 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨6, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41931918115229 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226875088291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_7 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41914537431927 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113439536037 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨7, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41914537431927 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113439536037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_8 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83794338124549 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226883050341 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨8, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83794338124549 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226883050341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_9 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83759625977373 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226887088041 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨9, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83759625977373 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226887088041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_10 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41862469193669 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226891075779 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨10, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41862469193669 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226891075779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_11 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83690275319637 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113447538993 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨11, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83690275319637 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113447538993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_12 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83655636739647 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113449550413 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨12, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83655636739647 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113449550413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_13 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83621022612923 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113451546041 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨13, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83621022612923 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113451546041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_14 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (208966082263 / 250000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113453557757 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨14, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (208966082263 / 250000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113453557757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_15 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (8355186758239 / 10000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (69590972449 / 3125000000000 : ℝ))
      (E := (cell12906 ⟨15, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (8355186758239 / 10000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (69590972449 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_16 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41758663305291 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113457552879 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨16, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41758663305291 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113457552879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_17 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83482809956041 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445383816511 / 20000000000000 : ℝ))
      (E := (cell12906 ⟨17, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83482809956041 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445383816511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_18 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (20862079396301 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226923111641 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨18, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (20862079396301 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226923111641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_19 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (16682769892937 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226927139199 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨19, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (16682769892937 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226927139199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12907_0 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (42036454474007 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556683625919 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨0, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (42036454474007 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556683625919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_1 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (42018999690383 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (222673848337 / 10000000000000 : ℝ))
      (E := (cell12907 ⟨1, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (42018999690383 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (222673848337 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_2 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (84003114655329 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226742469207 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨2, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (84003114655329 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226742469207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_3 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41984127367703 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113373234847 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨3, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41984127367703 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113373234847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_4 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (8393341958489 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226750493081 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨4, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (8393341958489 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226750493081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_5 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (10487326145983 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113377244707 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨5, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (10487326145983 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113377244707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_6 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83863823448599 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113379262167 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨6, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83863823448599 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113379262167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_7 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (16765812478311 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113381244667 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨7, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (16765812478311 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113381244667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_8 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (2618572686293 / 3125000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (278345813443 / 12500000000000 : ℝ))
      (E := (cell12907 ⟨8, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (2618572686293 / 3125000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (278345813443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_9 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (8375961412289 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113385263953 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨9, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (8375961412289 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113385263953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_10 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (10465615855139 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556693624753 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨10, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (10465615855139 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556693624753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_11 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83690264081237 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113389242647 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨11, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83690264081237 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113389242647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_12 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83655625808641 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556695623229 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨12, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83655625808641 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556695623229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_13 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (1045262649861 / 1250000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113393263897 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨13, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (1045262649861 / 1250000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113393263897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_14 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83586422587691 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113395268721 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨14, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83586422587691 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113395268721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_15 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83551857570987 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445358905443 / 20000000000000 : ℝ))
      (E := (cell12907 ⟨15, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83551857570987 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445358905443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_16 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (10439664613107 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (139174910027 / 6250000000000 : ℝ))
      (E := (cell12907 ⟨16, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (10439664613107 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (139174910027 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_17 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41741400277783 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (278350315697 / 12500000000000 : ℝ))
      (E := (cell12907 ⟨17, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41741400277783 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (278350315697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_18 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41724154244777 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (222680654371 / 10000000000000 : ℝ))
      (E := (cell12907 ⟨18, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41724154244777 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (222680654371 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_19 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41706920336717 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113405280509 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨19, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41706920336717 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113405280509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12908_0 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (2101822357547 / 2500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226617947227 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨0, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (2101822357547 / 2500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226617947227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_1 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (328273379089 / 390625000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (445324392341 / 20000000000000 : ℝ))
      (E := (cell12908 ⟨1, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (328273379089 / 390625000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (445324392341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_2 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (4200155031653 / 5000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (222662592521 / 10000000000000 : ℝ))
      (E := (cell12908 ⟨2, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (4200155031653 / 5000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (222662592521 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_3 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83968241024409 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113314980991 / 50000000000000 : ℝ))
      (E := (cell12908 ⟨3, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83968241024409 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113314980991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_4 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41966703092363 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (222663396449 / 10000000000000 : ℝ))
      (E := (cell12908 ⟨4, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41966703092363 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (222663396449 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_5 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (5243662254881 / 6250000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (139164871291 / 6250000000000 : ℝ))
      (E := (cell12908 ⟨5, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (5243662254881 / 6250000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (139164871291 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_6 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (8386381066879 / 10000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (55666048903 / 2500000000000 : ℝ))
      (E := (cell12908 ⟨6, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (8386381066879 / 10000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (55666048903 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_7 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83829049921269 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226645960371 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨7, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83829049921269 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226645960371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_8 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83794313800177 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226649960571 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨8, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83794313800177 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226649960571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_9 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41879801135173 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226653963629 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨9, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41879801135173 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226653963629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_10 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (20931228824197 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226657976207 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨10, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (20931228824197 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226657976207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_11 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41845126422351 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (17813295573 / 800000000000 : ℝ))
      (E := (cell12908 ⟨11, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41845126422351 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (17813295573 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_12 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83655614879463 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226665997201 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨12, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83655614879463 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226665997201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_13 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83621001366629 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556667489879 / 25000000000000 : ℝ))
      (E := (cell12908 ⟨13, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83621001366629 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556667489879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_14 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83586412271937 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (89066960543 / 4000000000000 : ℝ))
      (E := (cell12908 ⟨14, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83586412271937 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (89066960543 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_15 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83551847561301 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (278334748791 / 12500000000000 : ℝ))
      (E := (cell12908 ⟨15, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83551847561301 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (278334748791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_16 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (20879326800203 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556670502807 / 25000000000000 : ℝ))
      (E := (cell12908 ⟨16, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (20879326800203 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556670502807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_17 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (16696558231347 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113343011493 / 50000000000000 : ℝ))
      (E := (cell12908 ⟨17, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (16696558231347 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113343011493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_18 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (10431037424439 / 12500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226690030229 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨18, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (10431037424439 / 12500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226690030229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_19 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (16682766376751 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113347018673 / 50000000000000 : ℝ))
      (E := (cell12908 ⟨19, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (16682766376751 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113347018673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12909_0 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (84072879658017 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226501444129 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨0, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (84072879658017 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226501444129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_1 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (84037970715037 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226505435599 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨1, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (84037970715037 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226505435599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_2 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (84003086612987 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226509434689 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨2, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (84003086612987 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226509434689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_3 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83968227315571 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113256724953 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨3, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83968227315571 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113256724953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_4 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (16786678557337 / 20000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556629357893 / 25000000000000 : ℝ))
      (E := (cell12909 ⟨4, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (16786678557337 / 20000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556629357893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_5 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83898582990413 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226521445557 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨5, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83898582990413 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226521445557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_6 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (8386379789103 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113262720813 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨6, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (8386379789103 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113262720813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_7 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41914518726497 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113264713597 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨7, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41914518726497 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113264713597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_8 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83794301640953 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226533467439 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨8, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83794301640953 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226533467439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_9 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83759590419739 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (278317181657 / 12500000000000 : ℝ))
      (E := (cell12909 ⟨9, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83759590419739 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (278317181657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_10 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41862451877183 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (22265414493 / 1000000000000 : ℝ))
      (E := (cell12909 ⟨10, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41862451877183 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (22265414493 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_11 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (8369024161003 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113272730991 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨11, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (8369024161003 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113272730991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_12 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (5228475247007 / 6250000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (44530988787 / 2000000000000 : ℝ))
      (E := (cell12909 ⟨12, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (5228475247007 / 6250000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (44530988787 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_13 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (10452623843271 / 12500000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113276722693 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨13, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (10452623843271 / 12500000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113276722693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_14 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83586401957937 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113278742879 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨14, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83586401957937 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113278742879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_15 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41775918776667 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (222656150771 / 10000000000000 : ℝ))
      (E := (cell12909 ⟨15, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41775918776667 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (222656150771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_16 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83517297498449 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556641364537 / 25000000000000 : ℝ))
      (E := (cell12909 ⟨16, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83517297498449 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556641364537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_17 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (1669655635191 / 2000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226569516557 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨17, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (1669655635191 / 2000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226569516557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_18 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41724145151539 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226573512947 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨18, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41724145151539 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226573512947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_19 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (2606681971739 / 3125000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226577509911 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨19, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (2606681971739 / 3125000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226577509911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12910_0 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (42036432508213 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (44527698731 / 2000000000000 : ℝ))
      (E := (cell12910 ⟨0, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (42036432508213 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (44527698731 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_1 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (21009489096381 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226388962903 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨1, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (21009489096381 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226388962903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_2 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (84003072595111 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226392939763 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨2, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (84003072595111 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226392939763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_3 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41984106804447 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226396933461 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨3, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41984106804447 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226396933461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_4 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83933379390767 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (278300119031 / 12500000000000 : ℝ))
      (E := (cell12910 ⟨4, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83933379390767 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (278300119031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_5 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (5243660619051 / 6250000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226404946167 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨5, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (5243660619051 / 6250000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226404946167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_6 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83863785115317 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556602245213 / 25000000000000 : ℝ))
      (E := (cell12910 ⟨6, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83863785115317 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556602245213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_7 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83829024986731 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226412947797 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨7, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83829024986731 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226412947797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_8 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (10474286185463 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (222641697013 / 10000000000000 : ℝ))
      (E := (cell12910 ⟨8, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (10474286185463 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (222641697013 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_9 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83759578571069 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113210498393 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨9, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83759578571069 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113210498393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_10 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83724892213843 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113212488179 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨10, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83724892213843 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113212488179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_11 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83690230377223 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113214486637 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨11, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83690230377223 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113214486637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_12 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20913898256647 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (69576031053 / 3125000000000 : ℝ))
      (E := (cell12910 ⟨12, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20913898256647 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (69576031053 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_13 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41810490063749 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113218492701 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨13, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41810490063749 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113218492701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_14 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83586391645691 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226441012149 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨14, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83586391645691 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226441012149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_15 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83551827547083 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226445021179 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨15, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83551827547083 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226445021179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_16 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41758643898883 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556612254401 / 25000000000000 : ℝ))
      (E := (cell12910 ⟨16, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41758643898883 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556612254401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_17 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (10435346545501 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (222645300629 / 10000000000000 : ℝ))
      (E := (cell12910 ⟨17, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (10435346545501 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (222645300629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_18 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83448281212251 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445291398373 / 20000000000000 : ℝ))
      (E := (cell12910 ⟨18, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83448281212251 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445291398373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_19 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (10426726788639 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556615259247 / 25000000000000 : ℝ))
      (E := (cell12910 ⟨19, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (10426726788639 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556615259247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12911_0 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (16814570075421 / 20000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226268482323 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨0, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (16814570075421 / 20000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226268482323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_1 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (21009485514561 / 25000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278284060721 / 12500000000000 : ℝ))
      (E := (cell12911 ⟨1, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (21009485514561 / 25000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278284060721 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_2 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (10500382322429 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278284562289 / 12500000000000 : ℝ))
      (E := (cell12911 ⟨2, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (10500382322429 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278284562289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_3 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (134349119847 / 160000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445256094111 / 20000000000000 : ℝ))
      (E := (cell12911 ⟨3, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (134349119847 / 160000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445256094111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_4 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (8393336599697 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (11131422343 / 500000000000 : ℝ))
      (E := (cell12911 ⟨4, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (8393336599697 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (11131422343 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_5 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (10487319602663 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226288500437 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨5, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (10487319602663 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226288500437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_6 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83863772341653 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226292515827 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨6, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83863772341653 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226292515827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_7 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41914506261239 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278287065273 / 12500000000000 : ℝ))
      (E := (cell12911 ⟨7, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41914506261239 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278287065273 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_8 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (20948569332107 / 25000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445260105333 / 20000000000000 : ℝ))
      (E := (cell12911 ⟨8, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (20948569332107 / 25000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445260105333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_9 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83759566724337 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226304536179 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨9, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83759566724337 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226304536179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_10 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83724880675221 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226308499317 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨10, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83724880675221 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226308499317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_11 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83690219146279 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113156269297 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨11, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83690219146279 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113156269297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_12 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83655582102891 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226316544019 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨12, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83655582102891 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226316544019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_13 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41810484755309 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278290065179 / 12500000000000 : ℝ))
      (E := (cell12911 ⟨13, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41810484755309 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278290065179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_14 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41793190667599 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (34786320853 / 1562500000000 : ℝ))
      (E := (cell12911 ⟨14, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41793190667599 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (34786320853 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_15 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83551817542549 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113164265369 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨15, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83551817542549 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113164265369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_16 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83517278098763 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113166257491 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨16, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83517278098763 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113166257491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_17 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (8348276297011 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (139146034401 / 6250000000000 : ℝ))
      (E := (cell12911 ⟨17, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (8348276297011 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (139146034401 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_18 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83448272123033 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445268105047 / 20000000000000 : ℝ))
      (E := (cell12911 ⟨18, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83448272123033 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445268105047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_19 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83413805524147 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226344560303 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨19, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83413805524147 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226344560303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12912_0 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (10509104467507 / 12500000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226152023617 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨0, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (10509104467507 / 12500000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226152023617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_1 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (42018963866599 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113078031023 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨1, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (42018963866599 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113078031023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_2 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (84003044565949 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113080026229 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨2, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (84003044565949 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113080026229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_3 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (16793637240403 / 20000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113082030593 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨3, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (16793637240403 / 20000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113082030593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_4 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (16786670521059 / 20000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (44523360771 / 2000000000000 : ℝ))
      (E := (cell12912 ⟨4, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (16786670521059 / 20000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (44523360771 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_5 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (20974635934969 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113086025209 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨5, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (20974635934969 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113086025209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_6 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (16772751914007 / 20000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226176046553 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨6, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (16772751914007 / 20000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226176046553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_7 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (16765800012047 / 20000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113090046179 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨7, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (16765800012047 / 20000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113090046179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_8 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41897132587563 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113092039513 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨8, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41897132587563 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113092039513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_9 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83759554879541 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445237614287 / 20000000000000 : ℝ))
      (E := (cell12912 ⟨9, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83759554879541 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445237614287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_10 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41862434569249 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226192076243 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨10, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41862434569249 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226192076243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_11 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83690207917197 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113098049927 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨11, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83690207917197 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113098049927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_12 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (4182778559051 / 5000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113100045159 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨12, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (4182778559051 / 5000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113100045159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_13 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83620958895527 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556551027903 / 25000000000000 : ℝ))
      (E := (cell12912 ⟨13, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83620958895527 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556551027903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_14 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41793185513229 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445241622249 / 20000000000000 : ℝ))
      (E := (cell12912 ⟨14, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41793185513229 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445241622249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_15 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83551807539731 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (278276511821 / 12500000000000 : ℝ))
      (E := (cell12912 ⟨15, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83551807539731 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (278276511821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_16 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (521982927509 / 625000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (69569253903 / 3125000000000 : ℝ))
      (E := (cell12912 ⟨16, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (521982927509 / 625000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (69569253903 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_17 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (652209012327 / 781250000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113110045353 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨17, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (652209012327 / 781250000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113110045353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_18 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83448263035421 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113112056529 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨18, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83448263035421 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113112056529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_19 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83413796740753 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556557034533 / 25000000000000 : ℝ))
      (E := (cell12912 ⟨19, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83413796740753 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556557034533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12913_0 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (21018205276319 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113017809133 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨0, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (21018205276319 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113017809133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_1 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (5252369588149 / 6250000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226039633887 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨1, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (5252369588149 / 6250000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226039633887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_2 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (84003030554661 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226043660083 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨2, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (84003030554661 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226043660083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_3 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83968172501813 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445209529491 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨3, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83968172501813 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445209529491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_4 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83933339215741 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226051662101 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨4, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83933339215741 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226051662101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_5 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (20974632665133 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226055654063 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨5, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (20974632665133 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226055654063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_6 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (16772749360093 / 20000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226059631001 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨6, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (16772749360093 / 20000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226059631001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_7 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83828987600003 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113031829161 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨7, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83828987600003 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113031829161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_8 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (20948563255949 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113033842617 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨8, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (20948563255949 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113033842617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_9 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83759543036681 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (11130358303 / 500000000000 : ℝ))
      (E := (cell12913 ⟨9, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83759543036681 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (11130358303 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_10 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41862428801837 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (139129728067 / 6250000000000 : ℝ))
      (E := (cell12913 ⟨10, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41862428801837 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (139129728067 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_11 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41845098344989 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445215931411 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨11, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41845098344989 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445215931411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_12 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41827780130487 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226083690709 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨12, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41827780130487 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226083690709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_13 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (3344837931289 / 4000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (139130481113 / 6250000000000 : ℝ))
      (E := (cell12913 ⟨13, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (3344837931289 / 4000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (139130481113 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_14 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (8358636071947 / 10000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (139130730247 / 6250000000000 : ℝ))
      (E := (cell12913 ⟨14, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (8358636071947 / 10000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (139130730247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_15 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83551797538629 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226095712671 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨15, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83551797538629 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226095712671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_16 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83517258705797 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226099672733 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨16, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83517258705797 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226099672733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_17 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (20870686046811 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226103685391 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨17, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (20870686046811 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226103685391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_18 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (16689650789883 / 20000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113053848543 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨18, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (16689650789883 / 20000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113053848543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_19 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83413787958929 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113055856101 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨19, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83413787958929 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113055856101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12914_0 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (16814561294553 / 20000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (222591926627 / 10000000000000 : ℝ))
      (E := (cell12914 ⟨0, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (16814561294553 / 20000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (222591926627 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_1 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (84037899089803 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225923259143 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨1, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (84037899089803 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225923259143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_2 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (84003016545567 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556481815827 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨2, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (84003016545567 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556481815827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_3 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83968158803769 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225931287263 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨3, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83968158803769 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225931287263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_4 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83933325828307 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225935281329 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨4, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83933325828307 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225935281329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_5 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83898517583271 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225939253421 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨5, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83898517583271 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225939253421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_6 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83863734032941 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225943269173 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨6, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83863734032941 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225943269173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_7 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83828975141779 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225947278071 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨7, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83828975141779 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225947278071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_8 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83794240874439 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225951287269 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨8, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83794240874439 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225951287269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_9 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (20939882798939 / 25000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225955303671 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨9, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (20939882798939 / 25000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225955303671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_10 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (334899384283 / 400000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556489818967 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨10, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (334899384283 / 400000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556489818967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_11 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83690185464621 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (445192653657 / 20000000000000 : ℝ))
      (E := (cell12914 ⟨11, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83690185464621 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (445192653657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_12 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41827774671377 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225967287077 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨12, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41827774671377 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225967287077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_13 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83620937670711 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225971280021 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨13, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83620937670711 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225971280021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_14 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41793175207117 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225975310871 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨14, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41793175207117 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225975310871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_15 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83551787539243 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (139123707929 / 6250000000000 : ℝ))
      (E := (cell12914 ⟨15, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83551787539243 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (139123707929 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_16 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (10439656126479 / 12500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (222598333311 / 10000000000000 : ℝ))
      (E := (cell12914 ⟨16, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (10439656126479 / 12500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (222598333311 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_17 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (3339309391931 / 4000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (222598733447 / 10000000000000 : ℝ))
      (E := (cell12914 ⟨17, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (3339309391931 / 4000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (222598733447 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_18 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (10431030608127 / 12500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (139124458473 / 6250000000000 : ℝ))
      (E := (cell12914 ⟨18, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (10431030608127 / 12500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (139124458473 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_19 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41706889589337 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556498835197 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨19, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41706889589337 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556498835197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12915_0 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (21018197960631 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112901454899 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨0, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (21018197960631 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112901454899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_1 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (21009471192863 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225806879963 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨1, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (21009471192863 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225806879963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_2 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (21000750634667 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (556452730003 / 25000000000000 : ℝ))
      (E := (cell12915 ⟨2, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (21000750634667 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (556452730003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_3 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41984072553941 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225814922711 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨3, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41984072553941 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225814922711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_4 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83933312442993 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112909448117 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨4, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83933312442993 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112909448117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_5 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41949252254047 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225822906443 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨5, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41949252254047 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225822906443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_6 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41931860633731 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (22258269031 / 1000000000000 : ℝ))
      (E := (cell12915 ⟨6, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41931860633731 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (22258269031 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_7 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (16765792537113 / 20000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225830893611 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨7, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (16765792537113 / 20000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225830893611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_8 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41897114363527 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225834943151 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨8, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41897114363527 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225834943151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_9 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83759519356767 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225838942609 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨9, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83759519356767 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225838942609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_10 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83724834539723 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (556460739159 / 25000000000000 : ℝ))
      (E := (cell12915 ⟨10, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83724834539723 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (556460739159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_11 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41845087120563 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445169386709 / 20000000000000 : ℝ))
      (E := (cell12915 ⟨11, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41845087120563 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445169386709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_12 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83655538426359 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225850937537 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨12, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83655538426359 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225850937537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_13 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41810463530493 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225854916387 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨13, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41810463530493 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225854916387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_14 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (334345360443 / 400000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445171786769 / 20000000000000 : ℝ))
      (E := (cell12915 ⟨14, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (334345360443 / 400000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445171786769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_15 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83551777541571 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (34779108393 / 1562500000000 : ℝ))
      (E := (cell12915 ⟨15, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83551777541571 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (34779108393 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_16 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41758619659773 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225866931411 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨16, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41758619659773 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225866931411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_17 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (20870681352737 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (556467744929 / 25000000000000 : ℝ))
      (E := (cell12915 ⟨17, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (20870681352737 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (556467744929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_18 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41724117891111 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (139117185641 / 6250000000000 : ℝ))
      (E := (cell12915 ⟨18, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41724117891111 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (139117185641 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_19 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (8341377039999 / 10000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445175793123 / 20000000000000 : ℝ))
      (E := (cell12915 ⟨19, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (8341377039999 / 10000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445175793123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12916_0 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (1681455544291 / 2000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112843274427 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨0, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (1681455544291 / 2000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112843274427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_1 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (84037870455333 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225690554203 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨1, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (84037870455333 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225690554203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_2 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (84002988533963 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225694572319 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨2, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (84002988533963 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225694572319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_3 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83968131414151 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (11128492769 / 500000000000 : ℝ))
      (E := (cell12916 ⟨3, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83968131414151 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (11128492769 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_4 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83933299059799 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112851282371 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨4, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83933299059799 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112851282371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_5 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41949245717499 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225706555183 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨5, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41949245717499 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225706555183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_6 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83863708504029 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225710590753 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨6, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83863708504029 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225710590753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_7 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83828950231359 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (111285728147 / 5000000000000 : ℝ))
      (E := (cell12916 ⟨7, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83828950231359 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (111285728147 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_8 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83794216581641 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (139107412179 / 6250000000000 : ℝ))
      (E := (cell12916 ⟨8, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83794216581641 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (139107412179 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_9 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (2617484609991 / 3125000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225722577417 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨9, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (2617484609991 / 3125000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225722577417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_10 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41862411505297 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556431643811 / 25000000000000 : ℝ))
      (E := (cell12916 ⟨10, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41862411505297 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556431643811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_11 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83690163019491 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225730594751 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨11, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83690163019491 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225730594751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_12 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (20913881877947 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (111286729199 / 5000000000000 : ℝ))
      (E := (cell12916 ⟨12, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (20913881877947 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (111286729199 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_13 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (10452614556631 / 12500000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225738606907 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨13, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (10452614556631 / 12500000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225738606907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_14 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83586329809017 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445148522207 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨14, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83586329809017 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445148522207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_15 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41775883772807 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112873300857 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨15, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41775883772807 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112873300857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_16 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41758614814469 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445150128451 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨16, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41758614814469 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445150128451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_17 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83482716025263 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225754621131 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨17, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83482716025263 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225754621131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_18 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41724113350517 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225758659401 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨18, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41724113350517 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225758659401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_19 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41706880811437 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225762644961 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨19, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41706880811437 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225762644961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12917_0 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (16814552517769 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225570241267 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨0, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (16814552517769 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225570241267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_1 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (16807571228289 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225574281861 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨1, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (16807571228289 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225574281861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_2 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (84002974531451 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225578278107 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨2, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (84002974531451 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225578278107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_3 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (5248007357661 / 6250000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112791148167 / 50000000000000 : ℝ))
      (E := (cell12917 ⟨3, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (5248007357661 / 6250000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112791148167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_4 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83933285678723 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278198285857 / 12500000000000 : ℝ))
      (E := (cell12917 ⟨4, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83933285678723 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278198285857 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_5 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (16779695672797 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225590257587 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨5, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (16779695672797 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225590257587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_6 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83863695742641 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225594274161 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨6, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83863695742641 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225594274161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_7 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83828937779161 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278199785757 / 12500000000000 : ℝ))
      (E := (cell12917 ⟨7, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83828937779161 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278199785757 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_8 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41897102219099 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225602300427 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨8, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41897102219099 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225602300427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_9 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83759495684591 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112803133067 / 50000000000000 : ℝ))
      (E := (cell12917 ⟨9, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83759495684591 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112803133067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_10 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83724811483363 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225610305889 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨10, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83724811483363 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225610305889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_11 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83690151799717 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (556403577497 / 25000000000000 : ℝ))
      (E := (cell12917 ⟨11, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83690151799717 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (556403577497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_12 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83655516599041 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445123656903 / 20000000000000 : ℝ))
      (E := (cell12917 ⟨12, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83655516599041 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445123656903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_13 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41810452923449 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445124458689 / 20000000000000 : ℝ))
      (E := (cell12917 ⟨13, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41810452923449 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445124458689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_14 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41793159754517 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225626284281 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨14, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41793159754517 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225626284281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_15 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (20887939387843 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278203790069 / 12500000000000 : ℝ))
      (E := (cell12917 ⟨15, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (20887939387843 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278203790069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_16 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (10439652492501 / 12500000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139102143189 / 6250000000000 : ℝ))
      (E := (cell12917 ⟨16, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (10439652492501 / 12500000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139102143189 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_17 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83482706641219 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139102394809 / 6250000000000 : ℝ))
      (E := (cell12917 ⟨17, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83482706641219 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139102394809 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_18 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83448217621451 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225642344751 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨18, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83448217621451 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225642344751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_19 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83413752847327 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (44512926411 / 2000000000000 : ℝ))
      (E := (cell12917 ⟨19, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83413752847327 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (44512926411 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12918_0 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (84072747965407 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225453987041 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨0, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (84072747965407 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225453987041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_1 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (42018920914893 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225458005089 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨1, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (42018920914893 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225458005089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_2 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (21000740132783 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112730989751 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨2, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (21000740132783 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112730989751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_3 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41984052016579 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225465976609 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨3, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41984052016579 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225465976609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_4 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41966636149883 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225470004651 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨4, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41966636149883 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225470004651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_5 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20974616323763 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225474013661 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨5, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20974616323763 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225474013661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_6 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (83863682983297 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225478011299 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨6, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (83863682983297 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225478011299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_7 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (8382892532897 / 10000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225482004969 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨7, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (8382892532897 / 10000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225482004969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_8 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41897096148363 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (69546437557 / 3125000000000 : ℝ))
      (E := (cell12918 ⟨8, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41897096148363 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (69546437557 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_9 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20939870962851 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445098001753 / 20000000000000 : ℝ))
      (E := (cell12918 ⟨9, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20939870962851 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445098001753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_10 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20931199989507 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556373508111 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨10, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20931199989507 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556373508111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_11 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20922535145451 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556374505293 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨11, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20922535145451 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556374505293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_12 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (83655505688117 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556375509787 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨12, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (83655505688117 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556375509787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_13 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (16724179048507 / 20000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225506034141 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨13, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (16724179048507 / 20000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225506034141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_14 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41793154605401 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112755005873 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨14, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41793154605401 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112755005873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_15 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (83551747558843 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (69547313609 / 3125000000000 : ℝ))
      (E := (cell12918 ⟨15, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (83551747558843 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (69547313609 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_16 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (16703442050551 / 20000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225518052339 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨16, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (16703442050551 / 20000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225518052339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_17 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (1304417144669 / 1562500000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225522067157 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨17, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (1304417144669 / 1562500000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225522067157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_18 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (5215513033967 / 6250000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225526026311 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨18, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (5215513033967 / 6250000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225526026311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_19 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20853436018337 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225530050661 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨19, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20853436018337 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225530050661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12919_0 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (16814546668847 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445067545669 / 20000000000000 : ℝ))
      (E := (cell12919 ⟨0, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (16814546668847 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445067545669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_1 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (84037827520357 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112670861941 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨1, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (84037827520357 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112670861941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_2 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (16800589306601 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225345734379 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨2, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (16800589306601 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225345734379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_3 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41984045172947 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225349710429 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨3, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41984045172947 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225349710429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_4 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83933258922927 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225353718127 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨4, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83933258922927 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225353718127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_5 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83898452228201 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112678882727 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨5, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83898452228201 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112678882727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_6 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83863670225997 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112680872097 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨6, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83863670225997 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112680872097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_7 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41914456440393 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556341429919 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨7, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41914456440393 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556341429919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_8 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (10474272519653 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225369757071 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨8, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (10474272519653 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225369757071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_9 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (1675189440403 / 2000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225373747267 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨9, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (1675189440403 / 2000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225373747267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_10 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (8372478843459 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112688877453 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨10, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (8372478843459 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112688877453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_11 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (334760517463 / 400000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225381786391 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨11, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (334760517463 / 400000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225381786391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_12 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (10456936847377 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556346447441 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨12, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (10456936847377 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556346447441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_13 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41810442319979 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112694885429 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨13, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41810442319979 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112694885429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_14 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (1044828736429 / 1250000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225393793427 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨14, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (1044828736429 / 1250000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225393793427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_15 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83551737568027 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112698902351 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨15, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83551737568027 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112698902351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_16 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83517200567179 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225401809787 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨16, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83517200567179 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225401809787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_17 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83482687878053 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225405813541 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨17, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83482687878053 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225405813541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_18 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41724099733549 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225409820583 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨18, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41724099733549 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225409820583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_19 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83413735300937 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225413777017 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨19, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83413735300937 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225413777017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12920_0 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (8407271872533 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225221523011 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨0, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (8407271872533 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225221523011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_1 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (84037813213157 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (22252254961 / 1000000000000 : ℝ))
      (E := (cell12920 ⟨1, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (84037813213157 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (22252254961 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_2 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (8400293253707 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (34769210701 / 1562500000000 : ℝ))
      (E := (cell12920 ⟨2, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (8400293253707 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (34769210701 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_3 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (5248004791299 / 6250000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112616748899 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨3, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (5248004791299 / 6250000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112616748899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_4 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41966622774103 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556309371303 / 25000000000000 : ℝ))
      (E := (cell12920 ⟨4, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41966622774103 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556309371303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_5 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (8389843916343 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278155189121 / 12500000000000 : ℝ))
      (E := (cell12920 ⟨5, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (8389843916343 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278155189121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_6 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83863657470741 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (111262276541 / 5000000000000 : ℝ))
      (E := (cell12920 ⟨6, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83863657470741 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (111262276541 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_7 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83828900434609 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556312386543 / 25000000000000 : ℝ))
      (E := (cell12920 ⟨7, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83828900434609 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556312386543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_8 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83794168019691 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445050701631 / 20000000000000 : ℝ))
      (E := (cell12920 ⟨8, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83794168019691 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445050701631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_9 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83759460190829 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225257539683 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨9, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83759460190829 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225257539683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_10 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (10465597114131 / 12500000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (139078845709 / 6250000000000 : ℝ))
      (E := (cell12920 ⟨10, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (10465597114131 / 12500000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (139078845709 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_11 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (16738023630311 / 20000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112632773779 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨11, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (16738023630311 / 20000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112632773779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_12 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41827741935869 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445053907273 / 20000000000000 : ℝ))
      (E := (cell12920 ⟨12, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41827741935869 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445053907273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_13 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83620874039167 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445054712347 / 20000000000000 : ℝ))
      (E := (cell12920 ⟨13, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83620874039167 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445054712347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_14 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83586288619587 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (222527757117 / 10000000000000 : ℝ))
      (E := (cell12920 ⟨14, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83586288619587 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (222527757117 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_15 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (3342069103157 / 4000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112640785007 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨15, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (3342069103157 / 4000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112640785007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_16 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (1043964886041 / 1250000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (222528556337 / 10000000000000 : ℝ))
      (E := (cell12920 ⟨16, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (1043964886041 / 1250000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (222528556337 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_17 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (8348267849893 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112644778049 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨17, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (8348267849893 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112644778049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_18 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83448190392327 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225293552813 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨18, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83448190392327 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225293552813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_19 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83413726530093 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278162194737 / 12500000000000 : ℝ))
      (E := (cell12920 ⟨19, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83413726530093 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278162194737 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12921_0 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (8407270410869 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225105313209 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨0, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (8407270410869 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225105313209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_1 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (16807559781637 / 20000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (139069332609 / 6250000000000 : ℝ))
      (E := (cell12921 ⟨1, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (16807559781637 / 20000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (139069332609 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_2 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (42001459271663 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (556278322209 / 25000000000000 : ℝ))
      (E := (cell12921 ⟨2, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (42001459271663 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (556278322209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_3 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83968062977829 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (556279320203 / 25000000000000 : ℝ))
      (E := (cell12921 ⟨3, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83968062977829 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (556279320203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_4 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83933232175601 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225121305907 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨4, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83933232175601 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225121305907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_5 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83898426100739 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225125314153 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨5, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83898426100739 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225125314153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_6 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83863644717527 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225129313207 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨6, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83863644717527 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225129313207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_7 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83828887990437 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (222513331047 / 10000000000000 : ℝ))
      (E := (cell12921 ⟨7, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83828887990437 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (222513331047 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_8 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (2618567371379 / 3125000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (556284328273 / 25000000000000 : ℝ))
      (E := (cell12921 ⟨8, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (2618567371379 / 3125000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (556284328273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_9 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (1046993104543 / 1250000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225141327973 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨9, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (1046993104543 / 1250000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225141327973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_10 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83724765393401 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445029060739 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨10, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83724765393401 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445029060739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_11 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83690106939219 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112574652337 / 50000000000000 : ℝ))
      (E := (cell12921 ⟨11, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83690106939219 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112574652337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_12 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41827736483141 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445030667413 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨12, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41827736483141 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445030667413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_13 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83620863440161 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445031469727 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨13, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83620863440161 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445031469727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_14 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83586278326603 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112580672487 / 50000000000000 : ℝ))
      (E := (cell12921 ⟨14, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83586278326603 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112580672487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_15 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41775858795767 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (89006613257 / 4000000000000 : ℝ))
      (E := (cell12921 ⟨15, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41775858795767 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (89006613257 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_16 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83517181201057 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445033874259 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨16, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83517181201057 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445033874259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_17 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (10435333640181 / 12500000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (69536667283 / 3125000000000 : ℝ))
      (E := (cell12921 ⟨17, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (10435333640181 / 12500000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (69536667283 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_18 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83448181319159 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225177339507 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨18, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83448181319159 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225177339507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_19 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83413717760817 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225181393299 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨19, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83413717760817 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225181393299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12922_0 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (21018172373579 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2224989098939 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨0, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (21018172373579 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2224989098939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_1 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (84037784605441 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2224993142959 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨1, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (84037784605441 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2224993142959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_2 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (84002904551773 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278124643287 / 12500000000000 : ℝ))
      (E := (cell12922 ⟨2, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (84002904551773 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278124643287 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_3 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83968049297027 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (17800008939 / 800000000000 : ℝ))
      (E := (cell12922 ⟨3, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83968049297027 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (17800008939 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_4 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83933218805113 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225005122287 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨4, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83933218805113 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225005122287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_5 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83898413040127 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225009111061 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨5, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83898413040127 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225009111061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_6 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (20965907991589 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112506574663 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨6, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (20965907991589 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112506574663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_7 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (5239304721767 / 6250000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112508564281 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨7, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (5239304721767 / 6250000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112508564281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_8 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83794143750533 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112510556933 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨8, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83794143750533 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112510556933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_9 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83759436537983 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (111251258509 / 5000000000000 : ℝ))
      (E := (cell12922 ⟨9, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83759436537983 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (111251258509 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_10 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (1674495077513 / 2000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225029130021 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨10, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (1674495077513 / 2000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225029130021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_11 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83690095728741 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112516586959 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨11, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83690095728741 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112516586959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_12 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (10456932757831 / 12500000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278129641719 / 12500000000000 : ℝ))
      (E := (cell12922 ⟨12, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (10456932757831 / 12500000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278129641719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_13 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83620852842941 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (445008237939 / 20000000000000 : ℝ))
      (E := (cell12922 ⟨13, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83620852842941 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (445008237939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_14 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (10448283504421 / 12500000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112522586499 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨14, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (10448283504421 / 12500000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112522586499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_15 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (2610990862683 / 3125000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225049147117 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨15, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (2610990862683 / 3125000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225049147117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_16 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83517171520509 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112526587679 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨16, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83517171520509 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112526587679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_17 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (20870664936401 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225057204419 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨17, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (20870664936401 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225057204419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_18 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (16689634449519 / 20000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225061180663 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨18, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (16689634449519 / 20000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225061180663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_19 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83413708993107 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112532583337 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨19, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83413708993107 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112532583337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12923_0 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (42036337441103 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556218234509 / 25000000000000 : ℝ))
      (E := (cell12923 ⟨0, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (42036337441103 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556218234509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_1 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (3361510812197 / 4000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (444975391949 / 20000000000000 : ℝ))
      (E := (cell12923 ⟨1, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (3361510812197 / 4000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (444975391949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_2 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (84002890562409 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (139055058843 / 6250000000000 : ℝ))
      (E := (cell12923 ⟨2, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (84002890562409 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (139055058843 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_3 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83968035618379 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112442474793 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨3, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83968035618379 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112442474793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_4 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83933205436741 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112444496139 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨4, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83933205436741 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112444496139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_5 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (16779679996319 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112446480821 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨5, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (16779679996319 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112446480821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_6 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83863619217227 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (278112122651 / 12500000000000 : ℝ))
      (E := (cell12923 ⟨6, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83863619217227 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (278112122651 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_7 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83828863108111 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (44498020009 / 2000000000000 : ℝ))
      (E := (cell12923 ⟨7, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83828863108111 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (44498020009 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_8 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41897065809453 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112452484249 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨8, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41897065809453 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112452484249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_9 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41879712357229 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224909008261 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨9, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41879712357229 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224909008261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_10 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83724742359793 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224913010327 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨10, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83724742359793 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224913010327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_11 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41845042260061 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224916981023 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨11, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41845042260061 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224916981023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_12 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (16731090232167 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (111246049227 / 5000000000000 : ℝ))
      (E := (cell12923 ⟨12, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (16731090232167 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (111246049227 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_13 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (16724168449501 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112462513391 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨13, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (16724168449501 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112462513391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_14 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83586257745881 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112464498543 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨14, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83586257745881 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112464498543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_15 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (8355169762189 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224933017093 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨15, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (8355169762189 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224933017093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_16 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83517161841637 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224937033763 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨16, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83517161841637 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224937033763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_17 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (417413251857 / 500000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556235262989 / 25000000000000 : ℝ))
      (E := (cell12923 ⟨17, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (417413251857 / 500000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556235262989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_18 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83448163177633 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224945018033 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨18, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83448163177633 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224945018033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_19 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83413700226963 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224949052851 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨19, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83413700226963 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224949052851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12924_0 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (84072660272361 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (4449513661 / 200000000000 : ℝ))
      (E := (cell12924 ⟨0, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (84072660272361 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (4449513661 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_1 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (16807551201327 / 20000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224760829961 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨1, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (16807551201327 / 20000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224760829961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_2 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (21000719143809 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (139047803003 / 6250000000000 : ℝ))
      (E := (cell12924 ⟨2, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (21000719143809 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (139047803003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_3 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83968021941883 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (44495376707 / 2000000000000 : ℝ))
      (E := (cell12924 ⟨3, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83968021941883 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (44495376707 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_4 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (20983298017621 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112386428979 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨4, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (20983298017621 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112386428979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_5 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83898386925141 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112388432949 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨5, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83898386925141 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112388432949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_6 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83863606470139 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112390433413 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨6, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83863606470139 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112390433413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_7 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41914425334977 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (111239243407 / 5000000000000 : ℝ))
      (E := (cell12924 ⟨7, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41914425334977 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (111239243407 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_8 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83794119489247 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224788876987 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨8, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83794119489247 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224788876987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_9 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83759412892863 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224792842221 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨9, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83759412892863 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224792842221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_10 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (8372473084583 / 10000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224796886549 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨10, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (8372473084583 / 10000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224796886549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_11 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83690073313359 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224800900259 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨11, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83690073313359 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224800900259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_12 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83655440260843 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224804889431 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨12, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83655440260843 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224804889431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_13 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41810415826927 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444961771979 / 20000000000000 : ℝ))
      (E := (cell12924 ⟨13, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41810415826927 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444961771979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_14 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41793123729071 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224812875399 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨14, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41793123729071 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224812875399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_15 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (16710337527927 / 20000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224816883171 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨15, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (16710337527927 / 20000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224816883171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_16 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83517152164439 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224820888309 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨16, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83517152164439 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224820888309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_17 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41741320499417 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (222482489567 / 10000000000000 : ℝ))
      (E := (cell12924 ⟨17, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41741320499417 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (222482489567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_18 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83448154109273 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224828909869 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨18, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83448154109273 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224828909869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_19 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41706845731193 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224832935279 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨19, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41706845731193 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224832935279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

end BstLean.Part268
