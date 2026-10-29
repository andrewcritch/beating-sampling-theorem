import BstLean.Part268CellShard6Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12500_20 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83382982734731 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138433747251 / 50000000000000 : ℝ))
      (E := (cell12500 ⟨20, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83382982734731 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138433747251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_21 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (2083710917361 / 2500000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276871524031 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨21, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (2083710917361 / 2500000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276871524031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_22 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41656957490743 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276875502767 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨22, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41656957490743 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276875502767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_23 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83279417562809 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276879493097 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨23, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83279417562809 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276879493097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_24 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (1040561805069 / 1250000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (227688349891 / 10000000000000 : ℝ))
      (E := (cell12500 ⟨24, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (1040561805069 / 1250000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (227688349891 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_25 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (832104954769 / 1000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455377493097 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨25, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (832104954769 / 1000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455377493097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_26 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (20794017686099 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (284611439121 / 12500000000000 : ℝ))
      (E := (cell12500 ⟨26, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (20794017686099 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (284611439121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_27 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (10392708771953 / 12500000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (71152983417 / 3125000000000 : ℝ))
      (E := (cell12500 ⟨27, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (10392708771953 / 12500000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (71152983417 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_28 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41553646869183 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276899512761 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨28, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41553646869183 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276899512761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_29 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83072941400569 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276903470597 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨29, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83072941400569 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276903470597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_30 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83038613130343 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276907462183 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨30, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83038613130343 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276907462183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_31 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (83004308895963 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276911489773 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨31, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (83004308895963 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276911489773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_32 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82970028665863 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138457748427 / 50000000000000 : ℝ))
      (E := (cell12500 ⟨32, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82970028665863 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138457748427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_33 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41467886204321 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (45538389703 / 2000000000000 : ℝ))
      (E := (cell12500 ⟨33, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41467886204321 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (45538389703 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_34 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (16580308018611 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276923456159 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨34, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (16580308018611 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276923456159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_35 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82867331688019 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569231867441 / 25000000000000 : ℝ))
      (E := (cell12500 ⟨35, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82867331688019 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569231867441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_36 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (5177071697663 / 6250000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569232867111 / 25000000000000 : ℝ))
      (E := (cell12500 ⟨36, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (5177071697663 / 6250000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569232867111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_37 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41399493243027 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569233877919 / 25000000000000 : ℝ))
      (E := (cell12500 ⟨37, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41399493243027 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569233877919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_38 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82764849627743 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276939482767 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨38, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82764849627743 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276939482767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_39 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (4136536827861 / 5000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (71154484357 / 3125000000000 : ℝ))
      (E := (cell12500 ⟨39, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (4136536827861 / 5000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (71154484357 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12501_20 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41691486795419 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276736595429 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨20, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41691486795419 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276736595429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_21 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41674213934719 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276740593997 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨21, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41674213934719 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276740593997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_22 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (5207119154683 / 6250000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276744600799 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨22, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (5207119154683 / 6250000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276744600799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_23 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83279409374251 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (71148392551 / 3125000000000 : ℝ))
      (E := (cell12501 ⟨23, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83279409374251 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (71148392551 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_24 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83244936534519 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (113837629851 / 5000000000000 : ℝ))
      (E := (cell12501 ⟨24, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83244936534519 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (113837629851 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_25 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83210487923011 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (142297287121 / 6250000000000 : ℝ))
      (E := (cell12501 ⟨25, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83210487923011 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (142297287121 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_26 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83176063507179 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569190138931 / 25000000000000 : ℝ))
      (E := (cell12501 ⟨26, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83176063507179 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569190138931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_27 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41570831627319 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276764602343 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨27, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41570831627319 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276764602343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_28 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83107287133171 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138384280737 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨28, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83107287133171 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138384280737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_29 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (20768233777681 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276772552633 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨29, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (20768233777681 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276772552633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_30 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (83038607155411 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276776578301 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨30, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (83038607155411 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276776578301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_31 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41502151617753 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276780582217 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨31, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41502151617753 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276780582217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_32 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (16594004663889 / 20000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (35574758849 / 1562500000000 : ℝ))
      (E := (cell12501 ⟨32, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (16594004663889 / 20000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (35574758849 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_33 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (3317430695033 / 4000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138394295473 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨33, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (3317430695033 / 4000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138394295473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_34 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41450767686703 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138396299513 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨34, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41450767686703 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138396299513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_35 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82867327281103 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (284599573981 / 12500000000000 : ℝ))
      (E := (cell12501 ⟨35, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82867327281103 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (284599573981 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_36 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82833143067991 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (284600071307 / 12500000000000 : ℝ))
      (E := (cell12501 ⟨36, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82833143067991 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (284600071307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_37 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (10349872837913 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569201148581 / 25000000000000 : ℝ))
      (E := (cell12501 ⟨37, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (10349872837913 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569201148581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_38 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (20691211539107 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138404273379 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨38, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (20691211539107 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138404273379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_39 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (20682683349227 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138406272733 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨39, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (20682683349227 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138406272733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12502_20 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83382964448647 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (284575718807 / 12500000000000 : ℝ))
      (E := (cell12502 ⟨20, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83382964448647 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (284575718807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_21 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (41674209523049 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138304859063 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨21, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (41674209523049 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138304859063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_22 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83313897969993 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276613694753 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨22, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83313897969993 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276613694753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_23 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83279401187277 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276617742787 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨23, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83279401187277 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276617742787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_24 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (41622464332531 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569155422783 / 25000000000000 : ℝ))
      (E := (cell12502 ⟨24, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (41622464332531 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569155422783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_25 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83210480370629 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569156429607 / 25000000000000 : ℝ))
      (E := (cell12502 ⟨25, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83210480370629 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569156429607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_26 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83176056271429 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276629711361 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨26, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83176056271429 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276629711361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_27 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (2078541408377 / 2500000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (284579216433 / 12500000000000 : ℝ))
      (E := (cell12502 ⟨27, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (2078541408377 / 2500000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (284579216433 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_28 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (20776820132341 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138318861621 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨28, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (20776820132341 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138318861621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_29 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (8307292882223 / 10000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276641689339 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨29, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (8307292882223 / 10000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276641689339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_30 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83038601181791 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276645690659 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨30, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83038601181791 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276645690659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_31 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (83004297576321 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276649729459 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨31, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (83004297576321 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276649729459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_32 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (4148500898713 / 5000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276653690679 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨32, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (4148500898713 / 5000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276653690679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_33 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (20733940586051 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138328846551 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨33, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (20733940586051 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138328846551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_34 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (82901530654913 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276661679707 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨34, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (82901530654913 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276661679707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_35 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (10358415359413 / 12500000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138332855187 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨35, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (10358415359413 / 12500000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138332855187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_36 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (41416569487227 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276669727581 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨36, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (41416569487227 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276669727581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_37 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (16559795784319 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276673732147 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨37, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (16559795784319 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276673732147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_38 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (20691210671529 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569169431167 / 25000000000000 : ℝ))
      (E := (cell12502 ⟨38, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (20691210671529 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569169431167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_39 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (82730730237561 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276681705513 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨39, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (82730730237561 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276681705513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12503_20 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41691477654079 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276474901323 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨20, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41691477654079 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276474901323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_21 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (4167420511221 / 5000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276478896419 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨21, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (4167420511221 / 5000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276478896419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_22 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41656944733341 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276482901237 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨22, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41656944733341 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276482901237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_23 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (83279393001887 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276486919903 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨23, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (83279393001887 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276486919903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_24 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (83244920797149 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276490897951 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨24, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (83244920797149 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276490897951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_25 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (10401309102469 / 12500000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276494897337 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨25, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (10401309102469 / 12500000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276494897337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_26 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41588024518573 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138249460739 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨26, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41588024518573 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138249460739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_27 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (83141649416949 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (227650291513 / 10000000000000 : ℝ))
      (E := (cell12503 ⟨27, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (83141649416949 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (227650291513 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_28 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16621454785389 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276506881173 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨28, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16621454785389 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276506881173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_29 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16614584507017 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569127720179 / 25000000000000 : ℝ))
      (E := (cell12503 ⟨29, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16614584507017 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569127720179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_30 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (83038595209481 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276514916247 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨30, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (83038595209481 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276514916247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_31 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (83004291918409 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138259436491 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨31, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (83004291918409 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138259436491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_32 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (20742503157577 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569130717471 / 25000000000000 : ℝ))
      (E := (cell12503 ⟨32, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (20742503157577 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569130717471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_33 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82935757313777 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276526908747 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨33, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82935757313777 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276526908747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_34 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (10362690742197 / 12500000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138265436981 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨34, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (10362690742197 / 12500000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138265436981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_35 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (2589603702207 / 3125000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569133720987 / 25000000000000 : ℝ))
      (E := (cell12503 ⟨35, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (2589603702207 / 3125000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569133720987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_36 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (20708283720499 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455307776237 / 20000000000000 : ℝ))
      (E := (cell12503 ⟨36, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (20708283720499 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455307776237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_37 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41399487570463 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (227654286649 / 10000000000000 : ℝ))
      (E := (cell12503 ⟨37, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41399487570463 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (227654286649 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_38 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16552967843361 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276546899137 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨38, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16552967843361 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276546899137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_39 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41365363539589 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138275460431 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨39, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41365363539589 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138275460431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12504_20 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (8338294616937 / 10000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (284543020569 / 12500000000000 : ℝ))
      (E := (cell12504 ⟨20, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (8338294616937 / 10000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (284543020569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_21 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (20837100351101 / 25000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138174064439 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨21, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (20837100351101 / 25000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138174064439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_22 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (650889695039 / 781250000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138176080977 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨22, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (650889695039 / 781250000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138176080977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_23 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (520496155113 / 625000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138178075657 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨23, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (520496155113 / 625000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138178075657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_24 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83244912930781 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276360159127 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨24, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83244912930781 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276360159127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_25 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (4160523263519 / 5000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (569091032667 / 25000000000000 : ℝ))
      (E := (cell12504 ⟨25, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (4160523263519 / 5000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (569091032667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_26 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (10397005225541 / 12500000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276368127681 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨26, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (10397005225541 / 12500000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276368127681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_27 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (16628328500049 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455274430669 / 20000000000000 : ℝ))
      (E := (cell12504 ⟨27, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (16628328500049 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455274430669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_28 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (16621453465183 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (14227350951 / 625000000000 : ℝ))
      (E := (cell12504 ⟨28, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (16621453465183 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (14227350951 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_29 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83072916249289 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227638012677 / 10000000000000 : ℝ))
      (E := (cell12504 ⟨29, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83072916249289 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227638012677 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_30 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (83038589238481 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276384138079 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨30, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (83038589238481 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276384138079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_31 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (10375535782721 / 12500000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276388129823 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨31, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (10375535782721 / 12500000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276388129823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_32 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82970007287589 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276392103953 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨32, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82970007287589 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276392103953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_33 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (16587150456909 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455279224151 / 20000000000000 : ℝ))
      (E := (cell12504 ⟨33, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (16587150456909 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455279224151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_34 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (16580304244279 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (284550015401 / 12500000000000 : ℝ))
      (E := (cell12504 ⟨34, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (16580304244279 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (284550015401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_35 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (4143365703353 / 5000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276404112577 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨35, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (4143365703353 / 5000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276404112577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_36 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (10354141348827 / 12500000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276408148541 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨36, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (10354141348827 / 12500000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276408148541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_37 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41399485680649 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227641211467 / 10000000000000 : ℝ))
      (E := (cell12504 ⟨37, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41399485680649 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227641211467 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_38 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82764835748497 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (142276008053 / 6250000000000 : ℝ))
      (E := (cell12504 ⟨38, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82764835748497 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (142276008053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_39 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82730723921759 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276420132811 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨39, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82730723921759 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276420132811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12505_20 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41691468516141 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284526677953 / 12500000000000 : ℝ))
      (E := (cell12505 ⟨20, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41691468516141 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284526677953 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_21 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83348392586049 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276217415503 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨21, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83348392586049 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276217415503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_22 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (3332554898597 / 4000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276221418593 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨22, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (3332554898597 / 4000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276221418593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_23 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (5204961039741 / 6250000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276225437017 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨23, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (5204961039741 / 6250000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276225437017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_24 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83244905065957 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276229416307 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨24, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83244905065957 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276229416307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_25 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83210457722513 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276233418419 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨25, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83210457722513 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276233418419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_26 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83176034572977 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276237388367 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨26, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83176034572977 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276237388367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_27 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (10392704448121 / 12500000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138120693841 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨27, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (10392704448121 / 12500000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138120693841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_28 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83107260726273 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276245419311 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨28, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83107260726273 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276245419311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_29 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41536454982421 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284531178437 / 12500000000000 : ℝ))
      (E := (cell12505 ⟨29, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41536454982421 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284531178437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_30 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (10379822908599 / 12500000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284531676831 / 12500000000000 : ℝ))
      (E := (cell12505 ⟨30, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (10379822908599 / 12500000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284531676831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_31 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (83004280606399 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276257382947 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨31, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (83004280606399 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276257382947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_32 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82970001946103 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138130696443 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨32, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82970001946103 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138130696443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_33 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82935747256507 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (227626538769 / 10000000000000 : ℝ))
      (E := (cell12505 ⟨33, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82935747256507 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (227626538769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_34 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (8290151650637 / 10000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138134713721 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨34, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (8290151650637 / 10000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138134713721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_35 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82867309664613 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276273396259 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨35, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82867309664613 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276273396259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_36 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (16566625340063 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276277412377 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨36, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (16566625340063 / 20000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276277412377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_37 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (8279896758271 / 10000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (569070354507 / 25000000000000 : ℝ))
      (E := (cell12505 ⟨37, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (8279896758271 / 10000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (569070354507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_38 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82764832281191 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (11381427069 / 500000000000 : ℝ))
      (E := (cell12505 ⟨38, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82764832281191 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (11381427069 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_39 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82730720765303 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (8891755469 / 390625000000 : ℝ))
      (E := (cell12505 ⟨39, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82730720765303 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (8891755469 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12506_20 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (16676585579379 / 20000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276082736799 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨20, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (16676585579379 / 20000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276082736799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_21 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (16669676753871 / 20000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (284510844537 / 12500000000000 : ℝ))
      (E := (cell12506 ⟨21, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (16669676753871 / 20000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (284510844537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_22 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83313863966479 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455218145893 / 20000000000000 : ℝ))
      (E := (cell12506 ⟨22, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83313863966479 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455218145893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_23 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41639684227607 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (284511847127 / 12500000000000 : ℝ))
      (E := (cell12506 ⟨23, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41639684227607 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (284511847127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_24 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (20811224300669 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138049363923 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨24, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (20811224300669 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138049363923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_25 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (1664209003523 / 2000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276102760593 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨25, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (1664209003523 / 2000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276102760593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_26 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (8317602734309 / 10000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276106761939 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨26, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (8317602734309 / 10000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276106761939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_27 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (83141628671117 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276110734993 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨27, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (83141628671117 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276110734993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_28 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41553627064009 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (91044589643 / 4000000000000 : ℝ))
      (E := (cell12506 ⟨28, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41553627064009 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (91044589643 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_29 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (5192056480109 / 6250000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276118724429 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨29, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (5192056480109 / 6250000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276118724429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_30 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (20759644325103 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569030686489 / 25000000000000 : ℝ))
      (E := (cell12506 ⟨30, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (20759644325103 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569030686489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_31 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (830042749523 / 1000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (142257921837 / 6250000000000 : ℝ))
      (E := (cell12506 ⟨31, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (830042749523 / 1000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (142257921837 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_32 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (1659399932117 / 2000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276130736683 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨32, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (1659399932117 / 2000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276130736683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_33 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41467871114831 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138067384059 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨33, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41467871114831 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138067384059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_34 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (33160604717 / 40000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138069364041 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨34, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (33160604717 / 40000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138069364041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_35 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (82867305263283 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455228546999 / 20000000000000 : ℝ))
      (E := (cell12506 ⟨35, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (82867305263283 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455228546999 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_36 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (20708280652773 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569036682833 / 25000000000000 : ℝ))
      (E := (cell12506 ⟨36, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (20708280652773 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569036682833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_37 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41399481902581 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569037679477 / 25000000000000 : ℝ))
      (E := (cell12506 ⟨37, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41399481902581 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569037679477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_38 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41382414407443 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569038688499 / 25000000000000 : ℝ))
      (E := (cell12506 ⟨38, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41382414407443 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569038688499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_39 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (82730717609811 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276158722623 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨39, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (82730717609811 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276158722623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12507_20 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (10422864845401 / 12500000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275952162339 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨20, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (10422864845401 / 12500000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275952162339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_21 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41674187477161 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137978075629 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨21, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41674187477161 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137978075629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_22 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (16662771093931 / 20000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (18207681223 / 800000000000 : ℝ))
      (E := (cell12507 ⟨22, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (16662771093931 / 20000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (18207681223 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_23 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (16655872055231 / 20000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275964112981 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨23, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (16655872055231 / 20000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275964112981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_24 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41622444670469 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137984076049 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨24, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41622444670469 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137984076049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_25 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (83210442631291 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227597215719 / 10000000000000 : ℝ))
      (E := (cell12507 ⟨25, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (83210442631291 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227597215719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_26 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20794005028667 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275976131599 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨26, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20794005028667 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275976131599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_27 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20785405439673 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455196027371 / 20000000000000 : ℝ))
      (E := (cell12507 ⟨27, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20785405439673 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455196027371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_28 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (1662144950623 / 2000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137992058727 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨28, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (1662144950623 / 2000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137992058727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_29 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41536448699997 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227598813451 / 10000000000000 : ℝ))
      (E := (cell12507 ⟨29, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41536448699997 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227598813451 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_30 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41519285666671 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137996066003 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨30, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41519285666671 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1137996066003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_31 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (5187766831217 / 6250000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275996112123 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨31, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (5187766831217 / 6250000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2275996112123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_32 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20742497816707 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276000135349 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨32, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20742497816707 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276000135349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_33 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82935737204011 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (142250259057 / 6250000000000 : ℝ))
      (E := (cell12507 ⟨33, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82935737204011 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (142250259057 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_34 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (10362688384973 / 12500000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276008142303 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨34, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (10362688384973 / 12500000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276008142303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_35 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (8286730086307 / 10000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276012128787 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨35, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (8286730086307 / 10000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276012128787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_36 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82833118522947 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1138008052703 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨36, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82833118522947 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1138008052703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_37 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82798960028653 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227602013163 / 10000000000000 : ℝ))
      (E := (cell12507 ⟨37, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82798960028653 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227602013163 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_38 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41382412674791 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276024149437 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨38, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41382412674791 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276024149437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_39 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82730714455281 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276028100491 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨39, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82730714455281 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276028100491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12508_20 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (4169145481561 / 5000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137910791863 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨20, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (4169145481561 / 5000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137910791863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_21 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83348366140949 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275825542107 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨21, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83348366140949 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275825542107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_22 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20828461743613 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568957393053 / 25000000000000 : ℝ))
      (E := (cell12508 ⟨22, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20828461743613 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568957393053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_23 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83279352098677 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137916780787 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨23, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83279352098677 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137916780787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_24 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (41622440740371 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275837572359 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨24, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (41622440740371 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275837572359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_25 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (16642087017587 / 20000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568960387459 / 25000000000000 : ℝ))
      (E := (cell12508 ⟨25, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (16642087017587 / 20000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568960387459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_26 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83176012887711 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275845555747 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨26, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83176012887711 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275845555747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_27 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (83141614847693 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568962383711 / 25000000000000 : ℝ))
      (E := (cell12508 ⟨27, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (83141614847693 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568962383711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_28 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20776810233917 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (71120423389 / 3125000000000 : ℝ))
      (E := (cell12508 ⟨28, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20776810233917 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (71120423389 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_29 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (10384111389949 / 12500000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275857540797 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨29, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (10384111389949 / 12500000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275857540797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_30 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (4151928268379 / 5000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275861572797 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨30, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (4151928268379 / 5000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275861572797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_31 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (16600852729583 / 20000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137932764829 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨31, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (16600852729583 / 20000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137932764829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_32 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (41484992964519 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275869530341 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨32, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (41484992964519 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275869530341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_33 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (82935732179553 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568968394159 / 25000000000000 : ℝ))
      (E := (cell12508 ⟨33, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (82935732179553 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568968394159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_34 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (82901502368223 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (227587755293 / 10000000000000 : ℝ))
      (E := (cell12508 ⟨34, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (82901502368223 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (227587755293 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_35 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20716824115993 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275881577637 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨35, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20716824115993 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275881577637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_36 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (2070827860897 / 2500000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137942767299 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨36, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (2070827860897 / 2500000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137942767299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_37 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20214588929 / 24414062500 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137944770937 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨37, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20214588929 / 24414062500 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137944770937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_38 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (82764821885279 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275893541441 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨38, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (82764821885279 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275893541441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_39 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (41365355650857 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137948766833 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨39, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (41365355650857 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137948766833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12509_20 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83382900500931 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137845529611 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨20, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83382900500931 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137845529611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_21 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (16669671465847 / 20000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275695045411 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨21, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (16669671465847 / 20000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275695045411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_22 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83313838480869 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137849522893 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨22, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83313838480869 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137849522893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_23 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (4163967196139 / 5000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275703064467 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨23, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (4163967196139 / 5000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275703064467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_24 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83244873622089 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137853523491 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨24, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83244873622089 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137853523491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_25 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83210427546083 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568927763821 / 25000000000000 : ℝ))
      (E := (cell12509 ⟨25, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83210427546083 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568927763821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_26 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41588002831109 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (142232189649 / 6250000000000 : ℝ))
      (E := (cell12509 ⟨26, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41588002831109 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (142232189649 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_27 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41570803969059 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275719045811 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨27, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41570803969059 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275719045811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_28 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83107234341573 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137861517029 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨28, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83107234341573 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137861517029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_29 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83072884840537 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137863500883 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨29, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83072884840537 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137863500883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_30 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (10379819925391 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275731009837 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨30, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (10379819925391 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275731009837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_31 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (83004257997627 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275735002001 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨31, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (83004257997627 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275735002001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_32 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82969980592479 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (284467379843 / 12500000000000 : ℝ))
      (E := (cell12509 ⟨32, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82969980592479 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (284467379843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_33 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82935727156287 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (227574300473 / 10000000000000 : ℝ))
      (E := (cell12509 ⟨33, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82935727156287 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (227574300473 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_34 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (10362687207227 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (284468377319 / 12500000000000 : ℝ))
      (E := (cell12509 ⟨34, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (10362687207227 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (284468377319 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_35 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (8286729206599 / 10000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137875511467 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨35, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (8286729206599 / 10000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137875511467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_36 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82833110349889 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137877509457 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨36, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82833110349889 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137877509457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_37 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82798952478753 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (284469875913 / 12500000000000 : ℝ))
      (E := (cell12509 ⟨37, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82798952478753 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (284469875913 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_38 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82764818421977 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137881523687 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨38, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82764818421977 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137881523687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_39 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82730708149109 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275767022151 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨39, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82730708149109 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275767022151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12510_20 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83382891372341 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137780294413 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨20, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83382891372341 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137780294413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_21 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83348348519181 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455112908921 / 20000000000000 : ℝ))
      (E := (cell12510 ⟨21, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83348348519181 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455112908921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_22 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41656914994453 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (568892143399 / 25000000000000 : ℝ))
      (E := (cell12510 ⟨22, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41656914994453 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (568892143399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_23 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (5204958484279 / 6250000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227557256333 / 10000000000000 : ℝ))
      (E := (cell12510 ⟨23, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (5204958484279 / 6250000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227557256333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_24 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83244865764977 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275576575969 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨24, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83244865764977 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275576575969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_25 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83210420005733 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275580556783 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨25, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83210420005733 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275580556783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_26 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (20793999609547 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275584567513 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨26, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (20793999609547 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275584567513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_27 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83141601029969 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275588552907 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨27, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83141601029969 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275588552907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_28 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (162318804197 / 195312500000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455118514857 / 20000000000000 : ℝ))
      (E := (cell12510 ⟨28, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (162318804197 / 195312500000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455118514857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_29 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83072878562829 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137798287943 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨29, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83072878562829 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137798287943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_30 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83038553439983 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455120112023 / 20000000000000 : ℝ))
      (E := (cell12510 ⟨30, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83038553439983 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455120112023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_31 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (83004252348609 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (45512090583 / 2000000000000 : ℝ))
      (E := (cell12510 ⟨31, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (83004252348609 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (45512090583 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_32 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82969975257151 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275608543477 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨32, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82969975257151 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275608543477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_33 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41467861067107 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275612546321 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨33, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41467861067107 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275612546321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_34 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82901492948563 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275616539171 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨34, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82901492948563 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275616539171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_35 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82867287669123 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227562052329 / 10000000000000 : ℝ))
      (E := (cell12510 ⟨35, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82867287669123 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227562052329 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_36 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (5177069141561 / 6250000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275624558351 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨36, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (5177069141561 / 6250000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275624558351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_37 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82798948705361 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137814263959 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨37, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82798948705361 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137814263959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_38 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41382407479837 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137816274937 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨38, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41382407479837 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137816274937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_39 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82730704997467 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137818282973 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨39, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82730704997467 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137818282973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12511_20 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (10422860280681 / 12500000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275430114283 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨20, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (10422860280681 / 12500000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275430114283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_21 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41674169855393 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (71107317383 / 3125000000000 : ℝ))
      (E := (cell12511 ⟨21, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41674169855393 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (71107317383 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_22 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41656910749281 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455087631129 / 20000000000000 : ℝ))
      (E := (cell12511 ⟨22, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41656910749281 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455087631129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_23 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83279327575729 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137721058247 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨23, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83279327575729 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137721058247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_24 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83244857909407 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275446159321 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨24, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83244857909407 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275446159321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_25 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (16642082493377 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (284431264089 / 12500000000000 : ℝ))
      (E := (cell12511 ⟨25, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (16642082493377 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (284431264089 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_26 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41587995607811 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137727077567 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨26, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41587995607811 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137727077567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_27 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83141594123243 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275458114561 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨27, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83141594123243 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275458114561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_28 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (4155361057877 / 5000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455092422137 / 20000000000000 : ℝ))
      (E := (cell12511 ⟨28, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (4155361057877 / 5000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455092422137 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_29 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (20768218071617 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275466146217 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨29, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (20768218071617 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275466146217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_30 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (83038547478147 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455094021329 / 20000000000000 : ℝ))
      (E := (cell12511 ⟨30, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (83038547478147 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455094021329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_31 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (4150212335043 / 5000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568868527777 / 25000000000000 : ℝ))
      (E := (cell12511 ⟨31, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (4150212335043 / 5000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568868527777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_32 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41484984961527 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275478103081 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨32, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41484984961527 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275478103081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_33 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (82935717113333 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137741071423 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨33, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (82935717113333 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137741071423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_34 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (5181343015029 / 6250000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275486114787 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨34, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (5181343015029 / 6250000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275486114787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_35 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (20716820818343 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137745068659 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨35, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (20716820818343 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137745068659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_36 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (82833102181139 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (142218384557 / 6250000000000 : ℝ))
      (E := (cell12511 ⟨36, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (82833102181139 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (142218384557 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_37 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (5174934058313 / 6250000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275498103719 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨37, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (5174934058313 / 6250000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275498103719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_38 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (20691202874593 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275502107623 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨38, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (20691202874593 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275502107623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_39 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41365350923393 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568876526587 / 25000000000000 : ℝ))
      (E := (cell12511 ⟨39, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41365350923393 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568876526587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12512_20 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83382873120253 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (227529975211 / 10000000000000 : ℝ))
      (E := (cell12512 ⟨20, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83382873120253 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (227529975211 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_21 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (5209270681503 / 6250000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275303763801 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨21, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (5209270681503 / 6250000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275303763801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_22 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41656906504919 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137653866813 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨22, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41656906504919 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137653866813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_23 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41639659702287 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275311782291 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨23, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41639659702287 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275311782291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_24 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83244850055377 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275315738687 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨24, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83244850055377 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275315738687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_25 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83210404929539 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275319781447 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨25, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83210404929539 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275319781447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_26 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83175983994519 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (71103866839 / 3125000000000 : ℝ))
      (E := (cell12512 ⟨26, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83175983994519 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (71103866839 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_27 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41570793608971 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (227532773077 / 10000000000000 : ℝ))
      (E := (cell12512 ⟨27, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41570793608971 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (227532773077 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_28 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83107214567601 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275331760153 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨28, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83107214567601 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275331760153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_29 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83072866011453 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (71104242851 / 3125000000000 : ℝ))
      (E := (cell12512 ⟨29, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83072866011453 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (71104242851 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_30 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41519270758809 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (455067953283 / 20000000000000 : ℝ))
      (E := (cell12512 ⟨30, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41519270758809 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (455067953283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_31 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (83004241054381 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (18202749983 / 800000000000 : ℝ))
      (E := (cell12512 ⟨31, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (83004241054381 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (18202749983 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_32 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82969964590187 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275347776099 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨32, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82969964590187 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275347776099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_33 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (20733928023411 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275351735743 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨33, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (20733928023411 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275351735743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_34 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41450741766759 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137677872701 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨34, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41450741766759 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137677872701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_35 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (16573455775747 / 20000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275359747797 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨35, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (16573455775747 / 20000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275359747797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_36 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82833098098379 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137681871981 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨36, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82833098098379 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137681871981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_37 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (20699735290423 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568841933677 / 25000000000000 : ℝ))
      (E := (cell12512 ⟨37, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (20699735290423 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568841933677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_38 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (8276480803807 / 10000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275371720621 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨38, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (8276480803807 / 10000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275371720621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_39 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41365349348533 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275375760769 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨39, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41365349348533 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275375760769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12513_20 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (20845715999189 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275169444049 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨20, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (20845715999189 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275169444049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_21 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83348322098969 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275173425521 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨21, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83348322098969 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275173425521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_22 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (20828451130683 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275177424153 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨22, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (20828451130683 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275177424153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_23 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41639655617499 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137590722031 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨23, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41639655617499 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137590722031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_24 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (10405605275361 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275185430773 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨24, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (10405605275361 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275185430773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_25 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (16642079478739 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455037889247 / 20000000000000 : ℝ))
      (E := (cell12513 ⟨25, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (16642079478739 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455037889247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_26 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41587988387439 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (35549897429 / 1562500000000 : ℝ))
      (E := (cell12513 ⟨26, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41587988387439 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (35549897429 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_27 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (16628316062813 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (35549959399 / 1562500000000 : ℝ))
      (E := (cell12513 ⟨27, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (16628316062813 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (35549959399 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_28 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83107207979047 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275201405793 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨28, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83107207979047 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275201405793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_29 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (10384107467223 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (113760269623 / 5000000000000 : ℝ))
      (E := (cell12513 ⟨29, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (10384107467223 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (113760269623 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_30 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (20759633889599 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275209422439 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨30, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (20759633889599 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275209422439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_31 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (83004235409169 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137606719727 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨31, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (83004235409169 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137606719727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_32 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (1659399185171 / 2000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (568804346727 / 25000000000000 : ℝ))
      (E := (cell12513 ⟨32, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (1659399185171 / 2000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (568804346727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_33 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (16587141415029 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137610721071 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨33, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (16587141415029 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137610721071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_34 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (20725369706931 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137612715509 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨34, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (20725369706931 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137612715509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_35 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (20716818621303 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137614706669 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨35, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (20716818621303 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137614706669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_36 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (16566618803339 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275233390137 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨36, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (16566618803339 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275233390137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_37 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41399468695707 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (568809355221 / 25000000000000 : ℝ))
      (E := (cell12513 ⟨37, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41399468695707 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (568809355221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_38 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (82764804578767 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (227524138887 / 10000000000000 : ℝ))
      (E := (cell12513 ⟨38, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (82764804578767 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (227524138887 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_39 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (20682673887077 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275245411797 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨39, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (20682673887077 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275245411797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12514_20 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (16676570974991 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275039131843 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨20, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (16676570974991 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275039131843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_21 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (20837078323887 / 25000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275043141419 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨21, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (20837078323887 / 25000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275043141419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_22 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (16662759207449 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275047168923 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨22, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (16662759207449 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275047168923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_23 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83279303067001 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275051160139 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨23, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83279303067001 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275051160139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_24 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83244834351939 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (18200440951 / 800000000000 : ℝ))
      (E := (cell12514 ⟨24, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83244834351939 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (18200440951 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_25 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (10401298732419 / 12500000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275059165457 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨25, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (10401298732419 / 12500000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275059165457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_26 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (831759695567 / 1000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275063128159 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨26, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (831759695567 / 1000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275063128159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_27 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (8314157341161 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275067126863 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨27, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (8314157341161 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275067126863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_28 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41553600695939 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (284383888257 / 12500000000000 : ℝ))
      (E := (cell12514 ⟨28, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41553600695939 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (284383888257 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_29 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (4153642673273 / 5000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137537563423 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨29, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (4153642673273 / 5000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137537563423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_30 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (83038529600481 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (568769783303 / 25000000000000 : ℝ))
      (E := (cell12514 ⟨30, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (83038529600481 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (568769783303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_31 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41502114882613 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275083127327 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨31, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41502114882613 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275083127327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_32 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41484976964071 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455017422227 / 20000000000000 : ℝ))
      (E := (cell12514 ⟨32, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41484976964071 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455017422227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_33 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41467851028919 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455018228983 / 20000000000000 : ℝ))
      (E := (cell12514 ⟨33, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41467851028919 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455018228983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_34 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82901474123083 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137547556523 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨34, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82901474123083 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137547556523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_35 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (20716817523201 / 25000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (284387391743 / 12500000000000 : ℝ))
      (E := (cell12514 ⟨35, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (20716817523201 / 25000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (284387391743 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_36 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41416544968043 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (568775787519 / 25000000000000 : ℝ))
      (E := (cell12514 ⟨36, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41416544968043 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (568775787519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_37 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82798933622173 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275107103593 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨37, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82798933622173 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275107103593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_38 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82764801120463 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275111112373 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨38, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82764801120463 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275111112373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_39 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (8273069240051 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137557559071 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨39, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (8273069240051 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137557559071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12515_20 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83382845754851 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568727233003 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨20, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83382845754851 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568727233003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_21 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83348304493783 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (284364113937 / 12500000000000 : ℝ))
      (E := (cell12515 ⟨21, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83348304493783 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (284364113937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_22 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (2603555861043 / 3125000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274916909627 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨22, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (2603555861043 / 3125000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274916909627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_23 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (10409911862573 / 12500000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (56873023263 / 2500000000000 : ℝ))
      (E := (cell12515 ⟨23, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (10409911862573 / 12500000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (56873023263 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_24 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (8324482650253 / 10000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274924919699 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨24, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (8324482650253 / 10000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274924919699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_25 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83210382326509 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137464440367 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨25, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83210382326509 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137464440367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_26 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83175962339983 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (14218330471 / 625000000000 : ℝ))
      (E := (cell12515 ⟨26, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83175962339983 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (14218330471 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_27 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83141566510579 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274936906749 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨27, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83141566510579 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274936906749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_28 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (20776798701523 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (227494091939 / 10000000000000 : ℝ))
      (E := (cell12515 ⟨28, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (20776798701523 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (227494091939 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_29 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41536423597241 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137472457959 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨29, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41536423597241 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137472457959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_30 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83038523643873 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137474449367 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨30, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83038523643873 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137474449367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_31 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (83004224122551 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568738217503 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨31, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (83004224122551 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568738217503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_32 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (20742487149741 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568739222559 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨32, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (20742487149741 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568739222559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_33 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41467848520861 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (18199687221 / 800000000000 : ℝ))
      (E := (cell12515 ⟨33, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41467848520861 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (18199687221 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_34 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41450734709797 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454992981733 / 20000000000000 : ℝ))
      (E := (cell12515 ⟨34, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41450734709797 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (454992981733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_35 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82867265701509 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137484454807 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨35, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82867265701509 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137484454807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_36 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82833085856553 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137486453253 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨36, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82833085856553 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137486453253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_37 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82798929853969 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (45499538003 / 2000000000000 : ℝ))
      (E := (cell12515 ⟨37, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82798929853969 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (45499538003 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_38 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41382398831579 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (284372611391 / 12500000000000 : ℝ))
      (E := (cell12515 ⟨38, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41382398831579 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (284372611391 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_39 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82730689253673 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137492439901 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨39, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82730689253673 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137492439901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12516_20 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41691418318221 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274778728039 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨20, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41691418318221 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274778728039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_21 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (3333931827747 / 4000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (454956547151 / 20000000000000 : ℝ))
      (E := (cell12516 ⟨21, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (3333931827747 / 4000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (454956547151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_22 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (20828444767781 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274786704577 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨22, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (20828444767781 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274786704577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_23 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (650619427623 / 781250000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274790696881 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨23, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (650619427623 / 781250000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274790696881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_24 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (4162240932733 / 5000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274794716543 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨24, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (4162240932733 / 5000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274794716543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_25 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83210374795167 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (284349838603 / 12500000000000 : ℝ))
      (E := (cell12516 ⟨25, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83210374795167 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (284349838603 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_26 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83175955124727 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (113740136773 / 5000000000000 : ℝ))
      (E := (cell12516 ⟨26, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83175955124727 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (113740136773 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_27 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (8314155961097 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274806741197 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨27, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (8314155961097 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274806741197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_28 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (8310718822169 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137405364451 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨28, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (8310718822169 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137405364451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_29 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83072840924849 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137407350603 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨29, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83072840924849 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137407350603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_30 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83038517688571 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (71088084969 / 3125000000000 : ℝ))
      (E := (cell12516 ⟨30, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83038517688571 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (71088084969 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_31 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (83004218481143 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274822726031 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨31, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (83004218481143 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274822726031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_32 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (16593988654203 / 20000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (284353340527 / 12500000000000 : ℝ))
      (E := (cell12516 ⟨32, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (16593988654203 / 20000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (284353340527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_33 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (20733923006699 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274830715277 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨33, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (20733923006699 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274830715277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_34 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82901464717257 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274834700699 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨34, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82901464717257 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274834700699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_35 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (2589601915979 / 3125000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274838681739 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨35, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (2589601915979 / 3125000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274838681739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_36 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (16566616355619 / 20000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137421359033 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨36, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (16566616355619 / 20000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137421359033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_37 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41399463043401 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274846693241 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨37, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41399463043401 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274846693241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_38 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82764794206851 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274850725139 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨38, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82764794206851 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274850725139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_39 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82730686107797 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274854696779 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨39, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82730686107797 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274854696779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12517_20 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83382827519729 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284331072273 / 12500000000000 : ℝ))
      (E := (cell12517 ⟨20, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83382827519729 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284331072273 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_21 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (10418535861903 / 12500000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274652555911 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨21, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (10418535861903 / 12500000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274652555911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_22 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83313770590489 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274656553773 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨22, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83313770590489 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274656553773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_23 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83279278572483 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274660575881 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨23, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83279278572483 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274660575881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_24 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83244810808329 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137332283879 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨24, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83244810808329 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137332283879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_25 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (3328414690613 / 4000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274668591349 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨25, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (3328414690613 / 4000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274668591349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_26 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83175947910933 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137336295829 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨26, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83175947910933 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137336295829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_27 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83141552712783 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284334571473 / 12500000000000 : ℝ))
      (E := (cell12517 ⟨27, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83141552712783 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284334571473 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_28 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (5194198852417 / 6250000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274680593039 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨28, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (5194198852417 / 6250000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274680593039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_29 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (1038410433207 / 1250000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284335574957 / 12500000000000 : ℝ))
      (E := (cell12517 ⟨29, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (1038410433207 / 1250000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284335574957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_30 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (3321540469383 / 4000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (454937718807 / 20000000000000 : ℝ))
      (E := (cell12517 ⟨30, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (3321540469383 / 4000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (454937718807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_31 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (83004212841003 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274692578347 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨31, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (83004212841003 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274692578347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_32 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41484968972147 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274696554533 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨32, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41484968972147 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274696554533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_33 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (4146784350653 / 5000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274700582871 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨33, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (4146784350653 / 5000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274700582871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_34 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (10362682502009 / 12500000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274704547737 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨34, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (10362682502009 / 12500000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274704547737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_35 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (4143362846113 / 5000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284338570943 / 12500000000000 : ℝ))
      (E := (cell12517 ⟨35, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (4143362846113 / 5000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (284338570943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_36 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82833077700711 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274712584757 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨36, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82833077700711 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274712584757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_37 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (2587466322521 / 3125000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568679135381 / 25000000000000 : ℝ))
      (E := (cell12517 ⟨37, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (2587466322521 / 3125000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568679135381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_38 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82764790751543 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137360277861 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨38, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82764790751543 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137360277861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_39 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (258533384259 / 312500000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568681142269 / 25000000000000 : ℝ))
      (E := (cell12517 ⟨39, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (258533384259 / 312500000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568681142269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12518_20 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83382818404711 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274518482449 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨20, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83382818404711 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274518482449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_21 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (20837069524607 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454904497707 / 20000000000000 : ℝ))
      (E := (cell12518 ⟨21, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (20837069524607 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454904497707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_22 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83313762111471 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454905291443 / 20000000000000 : ℝ))
      (E := (cell12518 ⟨22, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83313762111471 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454905291443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_23 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83279270410799 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274530509191 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨23, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83279270410799 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274530509191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_24 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83244802963537 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568633618337 / 25000000000000 : ℝ))
      (E := (cell12518 ⟨24, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83244802963537 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568633618337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_25 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41605179868491 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (142158654371 / 6250000000000 : ℝ))
      (E := (cell12518 ⟨25, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41605179868491 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (142158654371 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_26 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83175940698599 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137271251179 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨26, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83175940698599 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137271251179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_27 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83141545816017 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (284318307117 / 12500000000000 : ℝ))
      (E := (cell12518 ⟨27, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83141545816017 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (284318307117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_28 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (20776793764259 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274550453357 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨28, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (20776793764259 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274550453357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_29 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (5192051774351 / 6250000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (90982179773 / 4000000000000 : ℝ))
      (E := (cell12518 ⟨29, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (5192051774351 / 6250000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (90982179773 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_30 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (20759626445471 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274558465321 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨30, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (20759626445471 / 25000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274558465321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_31 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (83004207202129 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (56864062137 / 2500000000000 : ℝ))
      (E := (cell12518 ⟨31, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (83004207202129 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (56864062137 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_32 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82969932618801 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274566498273 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨32, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82969932618801 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274566498273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_33 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41467841000257 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (35540164147 / 1562500000000 : ℝ))
      (E := (cell12518 ⟨33, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41467841000257 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (35540164147 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_34 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41450727658019 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137287224891 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨34, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41450727658019 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137287224891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_35 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (16573450506861 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454915689961 / 20000000000000 : ℝ))
      (E := (cell12518 ⟨35, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (16573450506861 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454915689961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_36 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41416536812201 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (284322805993 / 12500000000000 : ℝ))
      (E := (cell12518 ⟨36, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41416536812201 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (284322805993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_37 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41399459277789 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137293251831 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨37, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41399459277789 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137293251831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_38 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (5172799206077 / 6250000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274590500247 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨38, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (5172799206077 / 6250000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274590500247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_39 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82730679818923 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568648624173 / 25000000000000 : ℝ))
      (E := (cell12518 ⟨39, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82730679818923 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568648624173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12519_20 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (20845702322847 / 25000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274388440833 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨20, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (20845702322847 / 25000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274388440833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_21 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83348269303287 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274392417059 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨21, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83348269303287 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274392417059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_22 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83313753634069 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (454879282981 / 20000000000000 : ℝ))
      (E := (cell12519 ⟨22, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83313753634069 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (454879282981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_23 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (20819815562673 / 25000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137200219241 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨23, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (20819815562673 / 25000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137200219241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_24 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83244795120283 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274404433311 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨24, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83244795120283 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274404433311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_25 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83210352210139 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (284301057667 / 12500000000000 : ℝ))
      (E := (cell12519 ⟨25, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83210352210139 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (284301057667 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_26 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (3327037339509 / 4000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137206204579 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨26, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (3327037339509 / 4000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137206204579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_27 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83141538920673 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568604113769 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨27, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83141538920673 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568604113769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_28 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83107168476783 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (9097681707 / 400000000000 : ℝ))
      (E := (cell12519 ⟨28, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83107168476783 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (9097681707 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_29 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (16614564424803 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137212221843 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨29, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (16614564424803 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137212221843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_30 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41519249915249 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (35537944529 / 1562500000000 : ℝ))
      (E := (cell12519 ⟨30, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41519249915249 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (35537944529 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_31 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (83004201564521 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274432447431 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨31, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (83004201564521 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274432447431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_32 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82969927294537 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274436438349 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨32, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82969927294537 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274436438349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_33 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82935676989157 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274440424323 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨33, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82935676989157 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274440424323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_34 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (16580290123431 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274444406833 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨34, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (16580290123431 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274444406833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_35 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41433624073731 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568612111437 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨35, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41433624073731 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568612111437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_36 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (5177066846823 / 6250000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137226212449 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨36, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (5177066846823 / 6250000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137226212449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_37 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82798914791519 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568614100919 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨37, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82798914791519 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568614100919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_38 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82764783843919 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137230220673 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨38, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82764783843919 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137230220673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_39 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41365338337963 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137232210461 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨39, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41365338337963 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137232210461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12520_20 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41691400089879 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (113712922667 / 5000000000000 : ℝ))
      (E := (cell12520 ⟨20, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41691400089879 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (113712922667 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_21 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41674130254901 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568565614513 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨21, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41674130254901 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568565614513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_22 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83313745158283 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568566606711 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨22, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83313745158283 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568566606711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_23 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41639627046081 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137135211043 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨23, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41639627046081 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137135211043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_24 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41622393639283 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568568611913 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨24, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41622393639283 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568568611913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_25 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41605172342397 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2842848061 / 125000000000 : ℝ))
      (E := (cell12520 ⟨25, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41605172342397 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2842848061 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_26 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83175926278311 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137141214431 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨26, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83175926278311 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137141214431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_27 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83141532026751 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137143224679 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨27, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83141532026751 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137143224679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_28 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (10388395237239 / 12500000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274290454773 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨28, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (10388395237239 / 12500000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274290454773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_29 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41536407929879 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274294447739 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨29, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41536407929879 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274294447739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_30 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (83038493880417 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568574607663 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨30, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (83038493880417 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568574607663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_31 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (4150209796409 / 5000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274302405683 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨31, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (4150209796409 / 5000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274302405683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_32 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (165939843943 / 200000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274306433309 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨32, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (165939843943 / 200000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274306433309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_33 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82935671978989 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274310456749 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨33, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82935671978989 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274310456749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_34 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41450722959711 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568578604723 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨34, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41450722959711 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568578604723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_35 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82867243761731 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274318438151 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨35, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82867243761731 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274318438151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_36 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82833065475007 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137161228493 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨36, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82833065475007 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137161228493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_37 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82798911028497 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454865283509 / 20000000000000 : ℝ))
      (E := (cell12520 ⟨37, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82798911028497 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454865283509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_38 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (20691195097901 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274330437703 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨38, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (20691195097901 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274330437703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_39 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (1292666773967 / 1562500000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (113716722959 / 5000000000000 : ℝ))
      (E := (cell12520 ⟨39, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (1292666773967 / 1562500000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (113716722959 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12521_20 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83382791069823 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274128519971 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨20, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83382791069823 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274128519971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_21 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83348251717971 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274132494949 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨21, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83348251717971 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274132494949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_22 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83313736684113 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137068246517 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨22, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83313736684113 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137068246517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_23 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (10409905741901 / 12500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454828092001 / 20000000000000 : ℝ))
      (E := (cell12521 ⟨23, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (10409905741901 / 12500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454828092001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_24 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83244779438387 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (71067014313 / 3125000000000 : ℝ))
      (E := (cell12521 ⟨24, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83244779438387 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (71067014313 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_25 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83210337160947 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137074245353 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨25, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83210337160947 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137074245353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_26 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (20793979767589 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (71067265721 / 3125000000000 : ℝ))
      (E := (cell12521 ⟨26, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (20793979767589 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (71067265721 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_27 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (10392690641781 / 12500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (227415649821 / 10000000000000 : ℝ))
      (E := (cell12521 ⟨27, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (10392690641781 / 12500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (227415649821 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_28 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (41553577660211 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274160478981 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨28, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (41553577660211 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274160478981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_29 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (83072809596843 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (284270563311 / 12500000000000 : ℝ))
      (E := (cell12521 ⟨29, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (83072809596843 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (284270563311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_30 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (2075962198291 / 2500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274168466207 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨30, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (2075962198291 / 2500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274168466207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_31 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (16600838058621 / 20000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274172477273 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨31, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (16600838058621 / 20000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274172477273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_32 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (8296991664969 / 10000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274176483153 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨32, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (8296991664969 / 10000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274176483153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_33 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (8293566697001 / 10000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (568545121389 / 25000000000000 : ℝ))
      (E := (cell12521 ⟨33, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (8293566697001 / 10000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (568545121389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_34 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (2072536030571 / 2500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274184485961 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨34, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (2072536030571 / 2500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274184485961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_35 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82867239377113 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (3638701577 / 160000000000 : ℝ))
      (E := (cell12521 ⟨35, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82867239377113 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (3638701577 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_36 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (258853316881 / 312500000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137096242787 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨36, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (258853316881 / 312500000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137096242787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_37 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82798907266509 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137098243307 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨37, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82798907266509 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137098243307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_38 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (41382388470143 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137100244661 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨38, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (41382388470143 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137100244661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_39 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82730670392809 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454840898811 / 20000000000000 : ℝ))
      (E := (cell12521 ⟨39, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82730670392809 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454840898811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12522_20 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83382781961581 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (35531227851 / 1562500000000 : ℝ))
      (E := (cell12522 ⟨20, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83382781961581 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (35531227851 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_21 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41674121463897 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137001293017 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨21, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41674121463897 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137001293017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_22 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83313728211557 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568501653369 / 25000000000000 : ℝ))
      (E := (cell12522 ⟨22, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83313728211557 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568501653369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_23 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (8327923777983 / 10000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274010610569 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨23, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (8327923777983 / 10000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274010610569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_24 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (650349778123 / 781250000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137007290557 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨24, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (650349778123 / 781250000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137007290557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_25 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41605164819299 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137009293527 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨25, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41605164819299 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137009293527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_26 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (83175911863861 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454804514677 / 20000000000000 : ℝ))
      (E := (cell12522 ⟨26, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (83175911863861 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454804514677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_27 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41570759121583 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274026601629 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨27, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41570759121583 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274026601629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_28 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41553574372157 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (113701527891 / 5000000000000 : ℝ))
      (E := (cell12522 ⟨28, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41553574372157 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (113701527891 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_29 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (10384100416909 / 12500000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274034561459 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨29, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (10384100416909 / 12500000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274034561459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_30 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (10379810248021 / 12500000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274038556519 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨30, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (10379810248021 / 12500000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274038556519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_31 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (16600836931859 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454808520737 / 20000000000000 : ℝ))
      (E := (cell12522 ⟨31, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (16600836931859 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454808520737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_32 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82969911329107 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274046587881 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨32, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82969911329107 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274046587881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_33 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82935661962219 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (227405056931 / 10000000000000 : ℝ))
      (E := (cell12522 ⟨33, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82935661962219 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (227405056931 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_34 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (5181339782963 / 6250000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274054549451 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨34, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (5181339782963 / 6250000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274054549451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_35 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41433617496803 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568514647043 / 25000000000000 : ℝ))
      (E := (cell12522 ⟨35, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41433617496803 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568514647043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_36 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (16566611465981 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274062569299 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨36, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (16566611465981 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274062569299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_37 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (20699725876389 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137033276111 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨37, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (20699725876389 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137033276111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_38 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (20691193372491 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137035298101 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨38, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (20691193372491 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137035298101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_39 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (5170666703293 / 6250000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454814916851 / 20000000000000 : ℝ))
      (E := (cell12522 ⟨39, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (5170666703293 / 6250000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (454814916851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12523_20 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83382772855031 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136934378673 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨20, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83382772855031 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136934378673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_21 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83348234139271 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568468182827 / 25000000000000 : ℝ))
      (E := (cell12523 ⟨21, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83348234139271 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568468182827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_22 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (10414214967577 / 12500000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (284234591233 / 12500000000000 : ℝ))
      (E := (cell12523 ⟨22, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (10414214967577 / 12500000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (284234591233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_23 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (20819807406507 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568470174697 / 25000000000000 : ℝ))
      (E := (cell12523 ⟨23, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (20819807406507 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568470174697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_24 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (41622381881319 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273884700237 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨24, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (41622381881319 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273884700237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_25 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83210322117747 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454777747569 / 20000000000000 : ℝ))
      (E := (cell12523 ⟨25, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83210322117747 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454777747569 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_26 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (10396988082353 / 12500000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454778539641 / 20000000000000 : ℝ))
      (E := (cell12523 ⟨26, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (10396988082353 / 12500000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454778539641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_27 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (2598172229797 / 3125000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273896701193 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨27, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (2598172229797 / 3125000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273896701193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_28 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (20776785542397 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (113695037487 / 5000000000000 : ℝ))
      (E := (cell12523 ⟨28, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (20776785542397 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (113695037487 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_29 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83072797075043 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273904729599 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨29, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83072797075043 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273904729599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_30 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (83038476037999 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (284238587699 / 12500000000000 : ℝ))
      (E := (cell12523 ⟨30, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (83038476037999 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (284238587699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_31 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (332016716107 / 400000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136956363201 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨31, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (332016716107 / 400000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136956363201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_32 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (331879624039 / 400000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (284239593437 / 12500000000000 : ℝ))
      (E := (cell12523 ⟨32, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (331879624039 / 400000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (284239593437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_33 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82935656955617 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273920708013 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨33, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82935656955617 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273920708013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_34 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (132642290933 / 160000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273924726543 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨34, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (132642290933 / 160000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273924726543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_35 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (8286723061121 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454785749159 / 20000000000000 : ℝ))
      (E := (cell12523 ⟨35, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (8286723061121 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454785749159 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_36 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (20708263314741 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (7106039713 / 312500000000 : ℝ))
      (E := (cell12523 ⟨36, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (20708263314741 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (7106039713 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_37 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82798899745639 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (284242091461 / 12500000000000 : ℝ))
      (E := (cell12523 ⟨37, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82798899745639 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (284242091461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_38 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82764770040639 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136970349831 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨38, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82764770040639 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136970349831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_39 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (41365332056763 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (113697236489 / 5000000000000 : ℝ))
      (E := (cell12523 ⟨39, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (41365332056763 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (113697236489 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12524_20 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41691381875087 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273738928093 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨20, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41691381875087 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273738928093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_21 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83348225352401 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273742930773 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨21, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83348225352401 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273742930773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_22 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83313711271289 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454749380101 / 20000000000000 : ℝ))
      (E := (cell12524 ⟨22, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83313711271289 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454749380101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_23 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83279221473801 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454750179931 / 20000000000000 : ℝ))
      (E := (cell12524 ⟨23, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83279221473801 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454750179931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_24 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (20811188981767 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (17763710407 / 781250000000 : ℝ))
      (E := (cell12524 ⟨24, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (20811188981767 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (17763710407 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_25 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83210314598393 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (56843973577 / 2500000000000 : ℝ))
      (E := (cell12524 ⟨25, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83210314598393 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (56843973577 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_26 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (16635179491049 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454752587187 / 20000000000000 : ℝ))
      (E := (cell12524 ⟨26, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (16635179491049 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454752587187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_27 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83141504465261 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136883456877 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨27, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83141504465261 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136883456877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_28 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83107135596241 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273770937847 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨28, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83107135596241 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273770937847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_29 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (16614558163231 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454754978793 / 20000000000000 : ℝ))
      (E := (cell12524 ⟨29, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (16614558163231 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454754978793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_30 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (83038470093133 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142111181339 / 6250000000000 : ℝ))
      (E := (cell12524 ⟨30, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (83038470093133 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142111181339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_31 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (8300417339547 / 10000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136891451971 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨31, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (8300417339547 / 10000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136891451971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_32 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (4148495034581 / 5000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136893451727 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨32, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (4148495034581 / 5000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136893451727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_33 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41467825975101 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136895450833 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨33, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41467825975101 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136895450833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_34 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82901427139991 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136897450029 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨34, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82901427139991 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136897450029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_35 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (3314689049197 / 4000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273798899879 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨35, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (3314689049197 / 4000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273798899879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_36 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (10354131148637 / 12500000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136901451079 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨36, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (10354131148637 / 12500000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136901451079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_37 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (16559779197351 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142112931731 / 6250000000000 : ℝ))
      (E := (cell12524 ⟨37, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (16559779197351 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142112931731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_38 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (8276476659231 / 10000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (568452729267 / 25000000000000 : ℝ))
      (E := (cell12524 ⟨38, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (8276476659231 / 10000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (568452729267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_39 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41365330487661 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (227381493063 / 10000000000000 : ℝ))
      (E := (cell12524 ⟨39, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41365330487661 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (227381493063 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

end BstLean.Part268
