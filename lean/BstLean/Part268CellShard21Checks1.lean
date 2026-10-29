import BstLean.Part268CellShard21Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12875_20 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83379669430691 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230557642819 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨20, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83379669430691 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230557642819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_21 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (52090775177 / 62500000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230561628167 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨21, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (52090775177 / 62500000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230561628167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_22 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (41655417650009 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557641415031 / 25000000000000 : ℝ))
      (E := (cell12875 ⟨22, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (41655417650009 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557641415031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_23 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83276454448411 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115284841929 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨23, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83276454448411 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115284841929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_24 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (10405262211977 / 12500000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (139410852763 / 6250000000000 : ℝ))
      (E := (cell12875 ⟨24, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (10405262211977 / 12500000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (139410852763 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_25 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (20801941252459 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230577660921 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨25, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (20801941252459 / 25000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230577660921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_26 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (519834102239 / 625000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (278822709799 / 12500000000000 : ℝ))
      (E := (cell12875 ⟨26, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (519834102239 / 625000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (278822709799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_27 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (519619823181 / 625000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230585699149 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨27, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (519619823181 / 625000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230585699149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_28 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (5194056939381 / 6250000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230589667003 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨28, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (5194056939381 / 6250000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230589667003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_29 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83070674289907 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557648425241 / 25000000000000 : ℝ))
      (E := (cell12875 ⟨29, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83070674289907 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557648425241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_30 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (83036461456817 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557649421469 / 25000000000000 : ℝ))
      (E := (cell12875 ⟨30, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (83036461456817 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (557649421469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_31 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (5187642031213 / 6250000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230601681831 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨31, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (5187642031213 / 6250000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230601681831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_32 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (10371013423303 / 12500000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230605690207 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨32, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (10371013423303 / 12500000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230605690207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_33 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82933966086767 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230609712157 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨33, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82933966086767 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230609712157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_34 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82899848569497 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230613748607 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨34, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82899848569497 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230613748607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_35 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82865754803833 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230617741611 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨35, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82865754803833 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230617741611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_36 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (41415842379573 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (278827718781 / 12500000000000 : ℝ))
      (E := (cell12875 ⟨36, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (41415842379573 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (278827718781 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_37 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (41398819202483 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115312858039 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨37, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (41398819202483 / 50000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115312858039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_38 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (323295373871 / 390625000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115314878247 / 50000000000000 : ℝ))
      (E := (cell12875 ⟨38, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (323295373871 / 390625000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (1115314878247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12875_39 : CellCertificate 12875 (220466354342377 / 2500000000000000 : ℝ) (1631404647345027 / 1000000000000000000 : ℝ) (329429106657121 / 10000000000000000 : ℝ)
    (cell12875 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · norm_num [cell12875]
  · have h := gap_lower (n := 12875) (a := (82729616647011 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230633753899 / 100000000000000 : ℝ))
      (E := (cell12875 ⟨39, by decide⟩).energy) (xi := (329429106657121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12875 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12875]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12875])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12875) (a := (82729616647011 / 100000000000000 : ℝ)) (b := (19994814457 / 12500000000000 : ℝ)) (q := (2230633753899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12875])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12875]

theorem cert12876_20 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83379660895613 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278805029797 / 12500000000000 : ℝ))
      (E := (cell12876 ⟨20, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83379660895613 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278805029797 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_21 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41672616026401 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230444271661 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨21, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41672616026401 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230444271661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_22 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (666486618991 / 800000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230448293959 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨22, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (666486618991 / 800000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230448293959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_23 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (832764468261 / 1000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230452250367 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨23, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (832764468261 / 1000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230452250367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_24 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41621045188457 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230456260821 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨24, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41621045188457 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230456260821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_25 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41603878996961 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (139403766873 / 6250000000000 : ℝ))
      (E := (cell12876 ⟨25, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41603878996961 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (139403766873 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_26 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (20793362411223 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230464280571 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨26, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (20793362411223 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230464280571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_27 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83139165297759 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115234147577 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨27, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83139165297759 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115234147577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_28 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41552452460311 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230472316013 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨28, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41552452460311 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230472316013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_29 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (41535334240871 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115238143353 / 50000000000000 : ℝ))
      (E := (cell12876 ⟨29, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (41535334240871 / 50000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (1115238143353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_30 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (83036455949543 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230480326057 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨30, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (83036455949543 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230480326057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_31 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (1296910426447 / 1562500000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230484318637 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨31, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (1296910426447 / 1562500000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230484318637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_32 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82968102479683 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278811040541 / 12500000000000 : ℝ))
      (E := (cell12876 ⟨32, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82968102479683 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278811040541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_33 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82933961479669 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446098468857 / 20000000000000 : ℝ))
      (E := (cell12876 ⟨33, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82933961479669 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446098468857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_34 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (20724961065407 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230496320809 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨34, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (20724961065407 / 25000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230496320809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_35 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82865750794779 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230500371823 / 100000000000000 : ℝ))
      (E := (cell12876 ⟨35, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82865750794779 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (2230500371823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_36 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (16566336209699 / 20000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446100864373 / 20000000000000 : ℝ))
      (E := (cell12876 ⟨36, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (16566336209699 / 20000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446100864373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_37 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (16559526998461 / 20000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278813543391 / 12500000000000 : ℝ))
      (E := (cell12876 ⟨37, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (16559526998461 / 20000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278813543391 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_38 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82763612595893 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446102477799 / 20000000000000 : ℝ))
      (E := (cell12876 ⟨38, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82763612595893 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (446102477799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12876_39 : CellCertificate 12876 (44091910340159 / 500000000000000 : ℝ) (1631277905056399 / 1000000000000000000 : ℝ) (2058768220959 / 62500000000000 : ℝ)
    (cell12876 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · norm_num [cell12876]
  · have h := gap_lower (n := 12876) (a := (82729613829097 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278814548567 / 12500000000000 : ℝ))
      (E := (cell12876 ⟨39, by decide⟩).energy) (xi := (2058768220959 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12876 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12876]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12876])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12876) (a := (82729613829097 / 100000000000000 : ℝ)) (b := (39986486349 / 25000000000000 : ℝ)) (q := (278814548567 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12876])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12876]

theorem cert12877_20 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (20844913090521 / 25000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (223032288847 / 10000000000000 : ℝ))
      (E := (cell12877 ⟨20, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (20844913090521 / 25000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (223032288847 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_21 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (16669044764783 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (446065382287 / 20000000000000 : ℝ))
      (E := (cell12877 ⟨21, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (16669044764783 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (446065382287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_22 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83310819449207 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230330924111 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨22, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83310819449207 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230330924111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_23 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83276439205227 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115167464981 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨23, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83276439205227 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115167464981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_24 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (16648416611883 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230338932213 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨24, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (16648416611883 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230338932213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_25 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83207750979373 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230342933857 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨25, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83207750979373 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230342933857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_26 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41586721466437 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230346937651 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨26, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41586721466437 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230346937651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_27 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (83139158887851 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115175473061 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨27, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (83139158887851 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115175473061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_28 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (16620979762481 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230354961563 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨28, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (16620979762481 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230354961563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_29 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41535331337399 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557589731883 / 25000000000000 : ℝ))
      (E := (cell12877 ⟨29, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41535331337399 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557589731883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_30 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41518225221727 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557590740713 / 25000000000000 : ℝ))
      (E := (cell12877 ⟨30, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41518225221727 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557590740713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_31 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41501131043479 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557591738023 / 25000000000000 : ℝ))
      (E := (cell12877 ⟨31, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41501131043479 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (557591738023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_32 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (16593619514811 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230370955137 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨32, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (16593619514811 / 20000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230370955137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_33 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82933956873649 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115187486569 / 50000000000000 : ℝ))
      (E := (cell12877 ⟨33, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82933956873649 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (1115187486569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_34 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82899839954801 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230379007019 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨34, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82899839954801 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230379007019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_35 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82865746786731 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230382998833 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨35, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82865746786731 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230382998833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_36 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (82831677338813 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230387007657 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨36, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (82831677338813 / 100000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230387007657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_37 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41398815790289 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230390975049 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨37, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41398815790289 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230390975049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_38 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (8276360948171 / 10000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230395018403 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨38, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (8276360948171 / 10000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230395018403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12877_39 : CellCertificate 12877 (88181100028921 / 1000000000000000 : ℝ) (815575591229609 / 500000000000000000 : ℝ) (65875345651643 / 2000000000000000 : ℝ)
    (cell12877 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · norm_num [cell12877]
  · have h := gap_lower (n := 12877) (a := (41364805506023 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230399020117 / 100000000000000 : ℝ))
      (E := (cell12877 ⟨39, by decide⟩).energy) (xi := (65875345651643 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12877 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12877]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12877])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12877) (a := (41364805506023 / 50000000000000 : ℝ)) (b := (79966688561 / 50000000000000 : ℝ)) (q := (2230399020117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12877])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12877]

theorem cert12878_20 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83379643830101 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (139387849569 / 6250000000000 : ℝ))
      (E := (cell12878 ⟨20, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83379643830101 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (139387849569 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_21 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83345215596539 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (139388100363 / 6250000000000 : ℝ))
      (E := (cell12878 ⟨21, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83345215596539 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (139388100363 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_22 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83310811526013 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557553402231 / 25000000000000 : ℝ))
      (E := (cell12878 ⟨22, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83310811526013 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (557553402231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_23 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83276431585793 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (278777200739 / 12500000000000 : ℝ))
      (E := (cell12878 ⟨23, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83276431585793 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (278777200739 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_24 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83242075743317 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230221599999 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨24, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83242075743317 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230221599999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_25 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (8320774396619 / 10000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (34847274909 / 1562500000000 : ℝ))
      (E := (cell12878 ⟨25, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (8320774396619 / 10000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (34847274909 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_26 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (16634687244437 / 20000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115114795599 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨26, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (16634687244437 / 20000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115114795599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_27 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83139152479237 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230233593593 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨27, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83139152479237 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230233593593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_28 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41552446352723 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230237603653 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨28, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41552446352723 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230237603653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_29 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (20767664217269 / 25000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (27878020293 / 1250000000000 : ℝ))
      (E := (cell12878 ⟨29, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (20767664217269 / 25000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (27878020293 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_30 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83036444938551 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (223024565479 / 10000000000000 : ℝ))
      (E := (cell12878 ⟨30, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83036444938551 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (223024565479 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_31 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (83002256882457 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230249640753 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨31, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (83002256882457 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230249640753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_32 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82968092669541 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (223025364121 / 10000000000000 : ℝ))
      (E := (cell12878 ⟨32, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82968092669541 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (223025364121 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_33 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41466976134353 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (446051531463 / 20000000000000 : ℝ))
      (E := (cell12878 ⟨33, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41466976134353 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (446051531463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_34 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (10362479456127 / 12500000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115130815683 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨34, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (10362479456127 / 12500000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115130815683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_35 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82865742779689 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230265681287 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨35, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82865742779689 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230265681287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_36 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82831673630103 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115134845141 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨36, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82831673630103 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115134845141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_37 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82797628169787 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230273658533 / 100000000000000 : ℝ))
      (E := (cell12878 ⟨37, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82797628169787 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (2230273658533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_38 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (41381803184213 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115138851717 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨38, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (41381803184213 / 50000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115138851717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12878_39 : CellCertificate 12878 (881783797826647 / 10000000000000000 : ℝ) (326204895909779 / 200000000000000000 : ℝ) (82337636342589 / 2500000000000000 : ℝ)
    (cell12878 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · norm_num [cell12878]
  · have h := gap_lower (n := 12878) (a := (82729608195859 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115140853691 / 50000000000000 : ℝ))
      (E := (cell12878 ⟨39, by decide⟩).energy) (xi := (82337636342589 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12878 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12878]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12878])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12878) (a := (82729608195859 / 100000000000000 : ℝ)) (b := (79960405417 / 50000000000000 : ℝ)) (q := (1115140853691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12878])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12878]

theorem cert12879_20 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41689817649833 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230088293981 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨20, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41689817649833 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230088293981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_21 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41672603685337 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115046148231 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨21, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41672603685337 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115046148231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_22 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41655401802147 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115048145027 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨22, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41655401802147 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115048145027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_23 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (20819105991949 / 25000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115050139109 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨23, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (20819105991949 / 25000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115050139109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_24 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (4162103421431 / 5000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115052132089 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨24, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (4162103421431 / 5000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115052132089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_25 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (20801934238593 / 25000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230108309337 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨25, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (20801934238593 / 25000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230108309337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_26 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (3326937180513 / 4000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (17422752341 / 781250000000 : ℝ))
      (E := (cell12879 ⟨26, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (3326937180513 / 4000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (17422752341 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_27 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (16627829214383 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557529074007 / 25000000000000 : ℝ))
      (E := (cell12879 ⟨27, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (16627829214383 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (557529074007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_28 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (83104886599743 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230120300767 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨28, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (83104886599743 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230120300767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_29 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41535325532287 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278765539491 / 12500000000000 : ℝ))
      (E := (cell12879 ⟨29, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41535325532287 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278765539491 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_30 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (5189777464677 / 6250000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230128343343 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨30, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (5189777464677 / 6250000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230128343343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_31 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (16600450335821 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (139383270379 / 6250000000000 : ℝ))
      (E := (cell12879 ⟨31, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (16600450335821 / 20000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (139383270379 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_32 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (4148404388307 / 5000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230136323971 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨32, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (4148404388307 / 5000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230136323971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_33 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82933947664841 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278767542277 / 12500000000000 : ℝ))
      (E := (cell12879 ⟨33, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82933947664841 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (278767542277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_34 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (5181239459017 / 6250000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115072184861 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨34, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (5181239459017 / 6250000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115072184861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_35 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82865738773653 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230148360539 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨35, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82865738773653 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230148360539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_36 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (41415834961181 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115076184871 / 50000000000000 : ℝ))
      (E := (cell12879 ⟨36, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (41415834961181 / 50000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (1115076184871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_37 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82797624759929 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230156338889 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨37, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82797624759929 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230156338889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_38 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (82763603256041 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230160385373 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨38, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (82763603256041 / 100000000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230160385373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12879_39 : CellCertificate 12879 (55109787463409 / 625000000000000 : ℝ) (815448898160421 / 500000000000000000 : ℝ) (329324366688777 / 10000000000000000 : ℝ)
    (cell12879 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · norm_num [cell12879]
  · have h := gap_lower (n := 12879) (a := (10341200672567 / 12500000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230164391589 / 100000000000000 : ℝ))
      (E := (cell12879 ⟨39, by decide⟩).energy) (xi := (329324366688777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12879 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12879]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12879])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12879) (a := (10341200672567 / 12500000000000 : ℝ)) (b := (39977061633 / 25000000000000 : ℝ)) (q := (2230164391589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12879])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12879]

theorem cert12880_20 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83379626770777 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (445994198221 / 20000000000000 : ℝ))
      (E := (cell12880 ⟨20, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83379626770777 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (445994198221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_21 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83345199146319 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (11149874917 / 500000000000 : ℝ))
      (E := (cell12880 ⟨21, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83345199146319 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (11149874917 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_22 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (5206924730253 / 6250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (278747378231 / 12500000000000 : ℝ))
      (E := (cell12880 ⟨22, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (5206924730253 / 6250000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (278747378231 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_23 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83276416351237 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229983005247 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨23, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83276416351237 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229983005247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_24 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (3329682444613 / 4000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (222998704153 / 10000000000000 : ℝ))
      (E := (cell12880 ⟨24, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (3329682444613 / 4000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (222998704153 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_25 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83207729943919 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (222999102093 / 10000000000000 : ℝ))
      (E := (cell12880 ⟨25, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83207729943919 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (222999102093 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_26 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41586711402397 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (278749375571 / 12500000000000 : ℝ))
      (E := (cell12880 ⟨26, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41586711402397 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (278749375571 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_27 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (16627827933177 / 20000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229999053429 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨27, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (16627827933177 / 20000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2229999053429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_28 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (83104880495297 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230003052907 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨28, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (83104880495297 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230003052907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_29 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (20767661315323 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115003531751 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨29, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (20767661315323 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115003531751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_30 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41518216966149 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230011028513 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨30, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41518216966149 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230011028513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_31 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41501123238451 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115007533291 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨31, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41501123238451 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115007533291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_32 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82968082863851 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115009531 / 50000000000 : ℝ))
      (E := (cell12880 ⟨32, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82968082863851 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115009531 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_33 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (20733485765513 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115011537223 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨33, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (20733485765513 / 25000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115011537223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_34 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82899827040569 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115013523109 / 50000000000000 : ℝ))
      (E := (cell12880 ⟨34, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82899827040569 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (1115013523109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_35 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41432867384311 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230031095239 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨35, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41432867384311 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230031095239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_36 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (82831666215591 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (223003510471 / 10000000000000 : ℝ))
      (E := (cell12880 ⟨36, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (82831666215591 / 100000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (223003510471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_37 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41398810675503 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (557509768703 / 25000000000000 : ℝ))
      (E := (cell12880 ⟨37, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41398810675503 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (557509768703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_38 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (41381800072277 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230043122939 / 100000000000000 : ℝ))
      (E := (cell12880 ⟨38, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (41381800072277 / 50000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (2230043122939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12880_39 : CellCertificate 12880 (17634588101039 / 200000000000000 : ℝ) (1630771132770473 / 1000000000000000000 : ℝ) (41162274026549 / 1250000000000000 : ℝ)
    (cell12880 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · norm_num [cell12880]
  · have h := gap_lower (n := 12880) (a := (3309184102643 / 4000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (278755884093 / 12500000000000 : ℝ))
      (E := (cell12880 ⟨39, by decide⟩).energy) (xi := (41162274026549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12880 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12880]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12880])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12880) (a := (3309184102643 / 4000000000000 : ℝ)) (b := (79947842107 / 50000000000000 : ℝ)) (q := (278755884093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12880])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12880]

theorem cert12881_20 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (16675923648687 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229853742769 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨20, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (16675923648687 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229853742769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_21 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41672595461737 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229857724939 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨21, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41672595461737 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229857724939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_22 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20827696941319 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114930878981 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨22, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20827696941319 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114930878981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_23 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41638204368057 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229865787001 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨23, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41638204368057 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229865787001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_24 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (8324205380343 / 10000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229869756887 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨24, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (8324205380343 / 10000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229869756887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_25 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83207722934831 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229873787367 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨25, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83207722934831 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229873787367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_26 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (83173416098091 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278734720549 / 12500000000000 : ℝ))
      (E := (cell12881 ⟨26, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (83173416098091 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278734720549 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_27 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20784783315287 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278735225917 / 12500000000000 : ℝ))
      (E := (cell12881 ⟨27, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20784783315287 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278735225917 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_28 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41552437196053 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229885801591 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨28, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41552437196053 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229885801591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_29 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (8307063945923 / 10000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278736225957 / 12500000000000 : ℝ))
      (E := (cell12881 ⟨29, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (8307063945923 / 10000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (278736225957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_30 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (20759107107737 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (222989376883 / 10000000000000 : ℝ))
      (E := (cell12881 ⟨30, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (20759107107737 / 25000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (222989376883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_31 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41501120637923 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (445979560751 / 20000000000000 : ℝ))
      (E := (cell12881 ⟨31, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41501120637923 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (445979560751 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_32 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (3318723118507 / 4000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229901796719 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨32, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (3318723118507 / 4000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229901796719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_33 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (82933938460339 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229905807403 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨33, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (82933938460339 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229905807403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_34 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (41449911368953 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (89196393469 / 4000000000000 : ℝ))
      (E := (cell12881 ⟨34, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (41449911368953 / 50000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (89196393469 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_35 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (82865730764597 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114956913369 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨35, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (82865730764597 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114956913369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_36 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (82831662509789 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114958918257 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨36, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (82831662509789 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114958918257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_37 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (10349702242877 / 12500000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229921866303 / 100000000000000 : ℝ))
      (E := (cell12881 ⟨37, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (10349702242877 / 12500000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (2229921866303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_38 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (16552719406793 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (445985171483 / 20000000000000 : ℝ))
      (E := (cell12881 ⟨38, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (16552719406793 / 20000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (445985171483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12881_39 : CellCertificate 12881 (881702214737919 / 10000000000000000 : ℝ) (407661122223301 / 250000000000000000 : ℝ) (65854404388023 / 2000000000000000 : ℝ)
    (cell12881 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · norm_num [cell12881]
  · have h := gap_lower (n := 12881) (a := (82729599752477 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114964934163 / 50000000000000 : ℝ))
      (E := (cell12881 ⟨39, by decide⟩).energy) (xi := (65854404388023 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12881 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12881]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12881])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12881) (a := (82729599752477 / 100000000000000 : ℝ)) (b := (159883123881 / 100000000000000 : ℝ)) (q := (1114964934163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12881])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12881]

theorem cert12882_20 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41689804858819 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229736548977 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨20, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41689804858819 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229736548977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_21 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41672591351069 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229740521083 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨21, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41672591351069 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229740521083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_22 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (10413847480997 / 12500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229744544741 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨22, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (10413847480997 / 12500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229744544741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_23 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20819100280607 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229748506747 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨23, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20819100280607 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229748506747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_24 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (10405255811617 / 12500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (222975252703 / 10000000000000 : ℝ))
      (E := (cell12882 ⟨24, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (10405255811617 / 12500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (222975252703 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_25 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41603857963553 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229756550239 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨25, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41603857963553 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229756550239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_26 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20793352348179 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (557440144781 / 25000000000000 : ℝ))
      (E := (cell12882 ⟨26, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20793352348179 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (557440144781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_27 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83139126857703 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (8919058231 / 400000000000 : ℝ))
      (E := (cell12882 ⟨27, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83139126857703 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (8919058231 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_28 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20776217072543 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114884273409 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨28, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20776217072543 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114884273409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_29 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83070633658389 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (222977254839 / 10000000000000 : ℝ))
      (E := (cell12882 ⟨29, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83070633658389 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (222977254839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_30 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83036422930781 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445955312859 / 20000000000000 : ℝ))
      (E := (cell12882 ⟨30, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83036422930781 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (445955312859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_31 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (83002236075939 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114890298067 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨31, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (83002236075939 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114890298067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_32 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (8296807306261 / 10000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114892293353 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨32, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (8296807306261 / 10000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114892293353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_33 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (82933933859703 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229788595687 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨33, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (82933933859703 / 100000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229788595687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_34 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20724954609071 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229792623997 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨34, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20724954609071 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229792623997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_35 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (10358215845197 / 12500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114898306843 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨35, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (10358215845197 / 12500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114898306843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_36 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (20707914701239 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229800623827 / 100000000000000 : ℝ))
      (E := (cell12882 ⟨36, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (20707914701239 / 25000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (2229800623827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_37 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (2069940363399 / 2500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114902297987 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨37, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (2069940363399 / 2500000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114902297987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_38 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (3310543756971 / 4000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114904323759 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨38, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (3310543756971 / 4000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114904323759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12882_39 : CellCertificate 12882 (440837514235751 / 5000000000000000 : ℝ) (1630517864684451 / 1000000000000000000 : ℝ) (329245855870859 / 10000000000000000 : ℝ)
    (cell12882 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · norm_num [cell12882]
  · have h := gap_lower (n := 12882) (a := (41364798469871 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114906301057 / 50000000000000 : ℝ))
      (E := (cell12882 ⟨39, by decide⟩).energy) (xi := (329245855870859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12882 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12882]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12882])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12882) (a := (41364798469871 / 50000000000000 : ℝ)) (b := (39967641383 / 25000000000000 : ℝ)) (q := (1114906301057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12882])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12882]

theorem cert12883_20 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83379601193387 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114809675717 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨20, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83379601193387 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114809675717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_21 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83345174482311 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (278702914189 / 12500000000000 : ℝ))
      (E := (cell12883 ⟨21, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83345174482311 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (278702914189 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_22 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (1666215438643 / 2000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114813663921 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨22, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (1666215438643 / 2000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114813663921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_23 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83276393510179 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (445926267917 / 20000000000000 : ℝ))
      (E := (cell12883 ⟨23, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83276393510179 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (445926267917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_24 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83242039183841 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229635351961 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨24, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83242039183841 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229635351961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_25 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41603854460373 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229639367957 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨25, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41603854460373 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229639367957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_26 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (20793350672167 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229643331891 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨26, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (20793350672167 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229643331891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_27 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83139120455549 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557411840783 / 25000000000000 : ℝ))
      (E := (cell12883 ⟨27, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83139120455549 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557411840783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_28 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83104862189493 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114825673537 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨28, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83104862189493 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114825673537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_29 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41535313929383 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114827672107 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨29, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41535313929383 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114827672107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_30 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41518208715899 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229659356379 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨30, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41518208715899 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229659356379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_31 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (83002230877179 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229663385171 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨31, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (83002230877179 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229663385171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_32 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82968068163657 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229667373387 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨32, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82968068163657 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229667373387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_33 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82933929260143 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229671380701 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨33, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82933929260143 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229671380701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_34 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82899814135703 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114837704017 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨34, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82899814135703 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114837704017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_35 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82865722759559 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229679397437 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨35, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82865722759559 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229679397437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_36 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (20707913775273 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229683407979 / 100000000000000 : ℝ))
      (E := (cell12883 ⟨36, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (20707913775273 / 25000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (2229683407979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_37 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82797611129837 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557421859977 / 25000000000000 : ℝ))
      (E := (cell12883 ⟨37, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82797611129837 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557421859977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_38 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (41381795407741 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114845717267 / 50000000000000 : ℝ))
      (E := (cell12883 ⟨38, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (41381795407741 / 50000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (1114845717267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12883_39 : CellCertificate 12883 (110205980781469 / 1250000000000000 : ℝ) (815195630069817 / 500000000000000000 : ℝ) (16460984700177 / 500000000000000 : ℝ)
    (cell12883 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · norm_num [cell12883]
  · have h := gap_lower (n := 12883) (a := (82729594127869 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557423862583 / 25000000000000 : ℝ))
      (E := (cell12883 ⟨39, by decide⟩).energy) (xi := (16460984700177 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12883 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12883]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12883])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12883) (a := (82729594127869 / 100000000000000 : ℝ)) (b := (79929004583 / 50000000000000 : ℝ)) (q := (557423862583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12883])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12883]

theorem cert12884_20 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83379592670681 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229502150139 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨20, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83379592670681 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229502150139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_21 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (10418145782999 / 12500000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557376540137 / 25000000000000 : ℝ))
      (E := (cell12884 ⟨21, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (10418145782999 / 12500000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557376540137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_22 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (16662152803559 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229510165611 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨22, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (16662152803559 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229510165611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_23 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (16655277179873 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445902833757 / 20000000000000 : ℝ))
      (E := (cell12884 ⟨23, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (16655277179873 / 20000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (445902833757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_24 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41621015938073 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (222951817329 / 10000000000000 : ℝ))
      (E := (cell12884 ⟨24, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41621015938073 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (222951817329 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_25 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83207701915749 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (222952218211 / 10000000000000 : ℝ))
      (E := (cell12884 ⟨25, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83207701915749 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (222952218211 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_26 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (20793348996487 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229526198003 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨26, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (20793348996487 / 25000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229526198003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_27 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83139114054687 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229530165023 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨27, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83139114054687 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229530165023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_28 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83104856090069 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (55738355059 / 2500000000000 : ℝ))
      (E := (cell12884 ⟨28, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83104856090069 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (55738355059 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_29 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (83070622060363 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229538195127 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨29, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (83070622060363 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229538195127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_30 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41518205966999 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229542203613 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨30, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41518205966999 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229542203613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_31 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41501112839783 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (1114773114709 / 50000000000000 : ℝ))
      (E := (cell12884 ⟨31, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41501112839783 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (1114773114709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_32 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (10371007908227 / 12500000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (278693776917 / 12500000000000 : ℝ))
      (E := (cell12884 ⟨32, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (10371007908227 / 12500000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (278693776917 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_33 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82933924661659 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557388555261 / 25000000000000 : ℝ))
      (E := (cell12884 ⟨33, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82933924661659 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (557388555261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_34 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82899809836161 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229558247463 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨34, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82899809836161 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229558247463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_35 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82865718758547 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229562236637 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨35, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82865718758547 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229562236637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_36 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82831651398197 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (55739156191 / 2500000000000 : ℝ))
      (E := (cell12884 ⟨36, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82831651398197 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (55739156191 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_37 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (82797607724647 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (278696277753 / 12500000000000 : ℝ))
      (E := (cell12884 ⟨37, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (82797607724647 / 100000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (278696277753 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_38 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41381793853793 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (111478713859 / 5000000000000 : ℝ))
      (E := (cell12884 ⟨38, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41381793853793 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (111478713859 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12884_39 : CellCertificate 12884 (881620668077721 / 10000000000000000 : ℝ) (407566168813543 / 250000000000000000 : ℝ) (164596768168537 / 5000000000000000 : ℝ)
    (cell12884 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · norm_num [cell12884]
  · have h := gap_lower (n := 12884) (a := (41364795658429 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229578236757 / 100000000000000 : ℝ))
      (E := (cell12884 ⟨39, by decide⟩).energy) (xi := (164596768168537 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12884 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12884]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12884])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12884) (a := (41364795658429 / 50000000000000 : ℝ)) (b := (159845454783 / 100000000000000 : ℝ)) (q := (2229578236757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12884])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12884]

theorem cert12885_20 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (1042244801869 / 1250000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (222938500339 / 10000000000000 : ℝ))
      (E := (cell12885 ⟨20, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (1042244801869 / 1250000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (222938500339 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_21 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (41672579023591 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229389003871 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨21, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (41672579023591 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229389003871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_22 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (83310756104913 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (278674124963 / 12500000000000 : ℝ))
      (E := (cell12885 ⟨22, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (83310756104913 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (278674124963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_23 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (83276378289987 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229397052713 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨23, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (83276378289987 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229397052713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_24 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (83242024569851 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229401049407 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨24, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (83242024569851 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229401049407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_25 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16641538982423 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114702525557 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨25, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16641538982423 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114702525557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_26 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16634677856911 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557352265147 / 25000000000000 : ℝ))
      (E := (cell12885 ⟨26, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16634677856911 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (557352265147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_27 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (16627821531023 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114706510943 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨27, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (16627821531023 / 20000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114706510943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_28 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (831048499919 / 1000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229417054193 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨28, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (831048499919 / 1000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229417054193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_29 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (41535308131589 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114710521313 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨29, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (41535308131589 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114710521313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_30 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (83036406437381 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229425047469 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨30, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (83036406437381 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229425047469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_31 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (830022204831 / 1000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114714535161 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨31, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (830022204831 / 1000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114714535161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_32 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (41484029184543 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229433053981 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨32, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (41484029184543 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229433053981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_33 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (331735680257 / 400000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (55735926453 / 2500000000000 : ℝ))
      (E := (cell12885 ⟨33, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (331735680257 / 400000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (55735926453 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_34 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (82899805537659 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114720541829 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨34, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (82899805537659 / 100000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114720541829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_35 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (41432857379269 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229445072643 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨35, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (41432857379269 / 50000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229445072643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_36 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (8283164769627 / 10000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229449084143 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨36, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (8283164769627 / 10000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229449084143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_37 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (8279760432039 / 10000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114726559203 / 50000000000000 : ℝ))
      (E := (cell12885 ⟨37, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (8279760432039 / 10000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (1114726559203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_38 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20690896150147 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229457116739 / 100000000000000 : ℝ))
      (E := (cell12885 ⟨38, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20690896150147 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (2229457116739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12885_39 : CellCertificate 12885 (440796746974231 / 5000000000000000 : ℝ) (1630138110023487 / 1000000000000000000 : ℝ) (41145922858797 / 1250000000000000 : ℝ)
    (cell12885 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · norm_num [cell12885]
  · have h := gap_lower (n := 12885) (a := (20682397126677 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (139341321101 / 6250000000000 : ℝ))
      (E := (cell12885 ⟨39, by decide⟩).energy) (xi := (41145922858797 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12885 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12885]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12885])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12885) (a := (20682397126677 / 25000000000000 : ℝ)) (b := (79916451191 / 50000000000000 : ℝ)) (q := (139341321101 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12885])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12885]

theorem cert12886_20 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41689787814951 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229267911189 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨20, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41689787814951 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229267911189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_21 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (2083628745797 / 2500000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229271901801 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨21, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (2083628745797 / 2500000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229271901801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_22 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83310748193501 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114637944233 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨22, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83310748193501 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114637944233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_23 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (16655274136409 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229279933003 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨23, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (16655274136409 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229279933003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_24 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (16648403452991 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229283921923 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨24, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (16648403452991 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229283921923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_25 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83207687909843 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114643958277 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨25, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83207687909843 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114643958277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_26 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83173382584489 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114645959823 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨26, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83173382584489 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114645959823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_27 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41569550628417 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114647966859 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨27, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41569550628417 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114647966859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_28 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (16620968778997 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114649980529 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨28, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (16620968778997 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114649980529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_29 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (20767652616803 / 25000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114651972607 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨29, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (20767652616803 / 25000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114651972607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_30 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83036400941947 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114653973237 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨30, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83036400941947 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114653973237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_31 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (83002215287781 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114655983219 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨31, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (83002215287781 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114655983219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_32 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82968053473467 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229315947897 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨32, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82968053473467 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229315947897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_33 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (16586783093583 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (34833124227 / 1562500000000 : ℝ))
      (E := (cell12886 ⟨33, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (16586783093583 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (34833124227 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_34 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (20724950310049 / 25000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114661987623 / 50000000000000 : ℝ))
      (E := (cell12886 ⟨34, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (20724950310049 / 25000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (1114661987623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_35 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (41432855379767 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229327964099 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨35, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (41432855379767 / 50000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229327964099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_36 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82831643995311 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229331976157 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨36, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82831643995311 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229331976157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_37 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (16559520183413 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (445867202333 / 20000000000000 : ℝ))
      (E := (cell12886 ⟨37, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (16559520183413 / 20000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (445867202333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_38 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82763581494487 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229340011929 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨38, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82763581494487 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229340011929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12886_39 : CellCertificate 12886 (881566323863029 / 10000000000000000 : ℝ) (1630011564443 / 1000000000000000 : ℝ) (164570616801181 / 5000000000000000 : ℝ)
    (cell12886 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · norm_num [cell12886]
  · have h := gap_lower (n := 12886) (a := (82729585697421 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229343976681 / 100000000000000 : ℝ))
      (E := (cell12886 ⟨39, by decide⟩).energy) (xi := (164570616801181 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12886 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12886]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12886])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12886) (a := (82729585697421 / 100000000000000 : ℝ)) (b := (39955087991 / 25000000000000 : ℝ)) (q := (2229343976681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12886])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12886]

theorem cert12887_20 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (83379567111829 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (55728770381 / 2500000000000 : ℝ))
      (E := (cell12887 ⟨20, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (83379567111829 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (55728770381 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_21 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (16669028323617 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229154796021 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨21, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (16669028323617 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229154796021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_22 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41655370141781 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (278644853987 / 12500000000000 : ℝ))
      (E := (cell12887 ⟨22, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41655370141781 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (278644853987 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_23 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (83276363075537 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229162809657 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨23, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (83276363075537 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229162809657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_24 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (83242009961457 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229166849231 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨24, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (83242009961457 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229166849231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_25 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41603840454467 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114585418423 / 50000000000000 : ℝ))
      (E := (cell12887 ⟨25, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41603840454467 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114585418423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_26 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20793343971437 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229174833617 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨26, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20793343971437 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229174833617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_27 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41569547429921 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (139323677629 / 6250000000000 : ℝ))
      (E := (cell12887 ⟨27, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41569547429921 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (139323677629 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_28 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20776209449831 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229182864471 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨28, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20776209449831 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229182864471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_29 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (5191912792029 / 6250000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229186844389 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨29, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (5191912792029 / 6250000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229186844389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_30 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (16607279089539 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229190842103 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨30, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (16607279089539 / 20000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229190842103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_31 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (10375276261701 / 12500000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229194859213 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨31, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (10375276261701 / 12500000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229194859213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_32 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41484024289479 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229198897087 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨32, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41484024289479 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229198897087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_33 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (5183369429541 / 6250000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557300724567 / 25000000000000 : ℝ))
      (E := (cell12887 ⟨33, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (5183369429541 / 6250000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (557300724567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_34 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20724949235943 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229206863603 / 100000000000000 : ℝ))
      (E := (cell12887 ⟨34, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20724949235943 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (2229206863603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_35 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (20716426690383 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (222921091101 / 10000000000000 : ℝ))
      (E := (cell12887 ⟨35, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (20716426690383 / 25000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (222921091101 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_36 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (2070791007383 / 2500000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114607432507 / 50000000000000 : ℝ))
      (E := (cell12887 ⟨36, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (2070791007383 / 2500000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114607432507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_37 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (82797597514673 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114609450901 / 50000000000000 : ℝ))
      (E := (cell12887 ⟨37, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (82797597514673 / 100000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114609450901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_38 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41381789194641 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (445844580807 / 20000000000000 : ℝ))
      (E := (cell12887 ⟨38, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41381789194641 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (445844580807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12887_39 : CellCertificate 12887 (35261566312819 / 400000000000000 : ℝ) (1629885038508137 / 1000000000000000000 : ℝ) (329115088531949 / 10000000000000000 : ℝ)
    (cell12887 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · norm_num [cell12887]
  · have h := gap_lower (n := 12887) (a := (41364791444497 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114613465091 / 50000000000000 : ℝ))
      (E := (cell12887 ⟨39, by decide⟩).energy) (xi := (329115088531949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12887 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12887]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12887])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12887) (a := (41364791444497 / 50000000000000 : ℝ)) (b := (159807803527 / 100000000000000 : ℝ)) (q := (1114613465091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12887])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12887]

theorem cert12888_20 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83379558595299 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445806743109 / 20000000000000 : ℝ))
      (E := (cell12888 ⟨20, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83379558595299 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445806743109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_21 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83345133405797 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557259436213 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨21, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83345133405797 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557259436213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_22 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (20827683093773 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229041771657 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨22, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (20827683093773 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229041771657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_23 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83276355470463 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557261435261 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨23, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83276355470463 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557261435261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_24 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83242002659357 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114524886471 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨24, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83242002659357 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114524886471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_25 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83207673909387 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229053753577 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨25, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83207673909387 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229053753577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_26 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41586684594167 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (34829027251 / 1562500000000 : ℝ))
      (E := (cell12888 ⟨26, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41586684594167 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (34829027251 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_27 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83139088464141 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114530902691 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨27, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83139088464141 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114530902691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_28 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41552415852459 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114532882217 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨28, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41552415852459 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114532882217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_29 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41535299439467 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229069798659 / 100000000000000 : ℝ))
      (E := (cell12888 ⟨29, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41535299439467 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (2229069798659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_30 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (1297443593041 / 1562500000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (278634224111 / 12500000000000 : ℝ))
      (E := (cell12888 ⟨30, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (1297443593041 / 1562500000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (278634224111 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_31 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (83002204900581 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557269451801 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨31, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (83002204900581 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557269451801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_32 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82968043685559 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114540892199 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨32, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82968043685559 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114540892199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_33 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82933906278471 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114542892071 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨33, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82933906278471 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114542892071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_34 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (82899792648387 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445817961471 / 20000000000000 : ℝ))
      (E := (cell12888 ⟨34, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (82899792648387 / 100000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (445817961471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_35 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41432851382267 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (27863672451 / 1250000000000 : ℝ))
      (E := (cell12888 ⟨35, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41432851382267 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (27863672451 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_36 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (10353954574537 / 12500000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114548904693 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨36, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (10353954574537 / 12500000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114548904693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_37 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (20699398528303 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557275461879 / 25000000000000 : ℝ))
      (E := (cell12888 ⟨37, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (20699398528303 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (557275461879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_38 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (41381787642487 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (89164234071 / 4000000000000 : ℝ))
      (E := (cell12888 ⟨38, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (41381787642487 / 50000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (89164234071 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12888_39 : CellCertificate 12888 (176302399163971 / 2000000000000000 : ℝ) (814879266107161 / 500000000000000000 : ℝ) (164544473829027 / 5000000000000000 : ℝ)
    (cell12888 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · norm_num [cell12888]
  · have h := gap_lower (n := 12888) (a := (20682395020357 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114554910947 / 50000000000000 : ℝ))
      (E := (cell12888 ⟨39, by decide⟩).energy) (xi := (164544473829027 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12888 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12888]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12888])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12888) (a := (20682395020357 / 25000000000000 : ℝ)) (b := (15979525707 / 10000000000000 : ℝ)) (q := (1114554910947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12888])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12888]

theorem cert12889_20 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83379550080313 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (445783345739 / 20000000000000 : ℝ))
      (E := (cell12889 ⟨20, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83379550080313 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (445783345739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_21 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (10418140649377 / 12500000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228920689973 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨21, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (10418140649377 / 12500000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228920689973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_22 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41655362234047 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228924707743 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨22, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41655362234047 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228924707743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_23 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (10409543483353 / 12500000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228928727161 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨23, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (10409543483353 / 12500000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228928727161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_24 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (16648399071731 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (557233187861 / 25000000000000 : ℝ))
      (E := (cell12889 ⟨24, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (16648399071731 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (557233187861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_25 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41603833455601 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (55723418129 / 2500000000000 : ℝ))
      (E := (cell12889 ⟨25, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41603833455601 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (55723418129 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_26 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (16634672498449 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (139308794339 / 6250000000000 : ℝ))
      (E := (cell12889 ⟨26, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (16634672498449 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (139308794339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_27 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (83139082069729 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114472382607 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨27, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (83139082069729 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114472382607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_28 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (20776206402941 / 25000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (278618589929 / 12500000000000 : ℝ))
      (E := (cell12889 ⟨28, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (20776206402941 / 25000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (278618589929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_29 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41535296543311 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114476374757 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨29, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41535296543311 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114476374757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_30 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (16607276892547 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (445791348059 / 20000000000000 : ℝ))
      (E := (cell12889 ⟨30, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (16607276892547 / 20000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (445791348059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_31 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (830021997087 / 1000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114480375927 / 50000000000000 : ℝ))
      (E := (cell12889 ⟨31, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (830021997087 / 1000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (1114480375927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_32 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82968038793271 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228964785559 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨32, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82968038793271 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228964785559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_33 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (1036673771067 / 1250000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (139310548997 / 6250000000000 : ℝ))
      (E := (cell12889 ⟨33, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (1036673771067 / 1250000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (139310548997 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_34 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (2072494708851 / 2500000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228972806501 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨34, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (2072494708851 / 2500000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228972806501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_35 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41432849384269 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (557244198813 / 25000000000000 : ℝ))
      (E := (cell12889 ⟨35, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41432849384269 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (557244198813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_36 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (258848852807 / 312500000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (222898080927 / 10000000000000 : ℝ))
      (E := (cell12889 ⟨36, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (258848852807 / 312500000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (222898080927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_37 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (82797590712683 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228984790107 / 100000000000000 : ℝ))
      (E := (cell12889 ⟨37, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (82797590712683 / 100000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (2228984790107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_38 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (41381786090781 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (222898879643 / 10000000000000 : ℝ))
      (E := (cell12889 ⟨38, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (41381786090781 / 50000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (222898879643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12889_39 : CellCertificate 12889 (440742418930111 / 5000000000000000 : ℝ) (1629632045556983 / 1000000000000000000 : ℝ) (65812562195919 / 2000000000000000 : ℝ)
    (cell12889 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · norm_num [cell12889]
  · have h := gap_lower (n := 12889) (a := (20682394318681 / 25000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (55724820701 / 2500000000000 : ℝ))
      (E := (cell12889 ⟨39, by decide⟩).energy) (xi := (65812562195919 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12889 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12889]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12889])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12889) (a := (20682394318681 / 25000000000000 : ℝ)) (b := (31956542519 / 20000000000000 : ℝ)) (q := (55724820701 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12889])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12889]

theorem cert12890_20 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83379541566869 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445759935961 / 20000000000000 : ℝ))
      (E := (cell12890 ⟨20, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83379541566869 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445759935961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_21 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41672558492871 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114401844853 / 50000000000000 : ℝ))
      (E := (cell12890 ⟨21, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41672558492871 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114401844853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_22 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (16662143312513 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228807698503 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨22, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (16662143312513 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228807698503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_23 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41638170132309 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228811709647 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨23, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41638170132309 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228811709647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_24 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83241988059351 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228815726351 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨24, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83241988059351 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228815726351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_25 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41603829957189 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445763938637 / 20000000000000 : ℝ))
      (E := (cell12890 ⟨25, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41603829957189 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445763938637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_26 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83173355797481 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (22288237297 / 1000000000000 : ℝ))
      (E := (cell12890 ⟨26, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83173355797481 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (22288237297 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_27 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (83139075676607 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (55720693039 / 2500000000000 : ℝ))
      (E := (cell12890 ⟨27, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (83139075676607 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (55720693039 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_28 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (10388102439983 / 12500000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445766345893 / 20000000000000 : ℝ))
      (E := (cell12890 ⟨28, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (10388102439983 / 12500000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445766345893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_29 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41535293647763 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228835755467 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨29, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41535293647763 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228835755467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_30 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (20759094743007 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228839742859 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨30, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (20759094743007 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228839742859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_31 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (16600438903593 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (55721093793 / 2500000000000 : ℝ))
      (E := (cell12890 ⟨31, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (16600438903593 / 20000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (55721093793 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_32 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (20742008475523 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (111442389171 / 5000000000000 : ℝ))
      (E := (cell12890 ⟨32, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (20742008475523 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (111442389171 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_33 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (82933897093323 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228851780497 / 100000000000000 : ℝ))
      (E := (cell12890 ⟨33, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (82933897093323 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (2228851780497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_34 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (20724946015183 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445771148759 / 20000000000000 : ℝ))
      (E := (cell12890 ⟨34, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (20724946015183 / 25000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (445771148759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_35 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41432847386773 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (17412967119 / 781250000000 : ℝ))
      (E := (cell12890 ⟨35, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41432847386773 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (17412967119 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_36 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (1656632584023 / 2000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114431903001 / 50000000000000 : ℝ))
      (E := (cell12890 ⟨36, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (1656632584023 / 2000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114431903001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_37 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41398793656543 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (89154711531 / 4000000000000 : ℝ))
      (E := (cell12890 ⟨37, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41398793656543 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (89154711531 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_38 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (41381784539523 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114435898361 / 50000000000000 : ℝ))
      (E := (cell12890 ⟨38, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (41381784539523 / 50000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114435898361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12890_39 : CellCertificate 12890 (88145768394063 / 1000000000000000 : ℝ) (407376394632887 / 250000000000000000 : ℝ) (329036678495491 / 10000000000000000 : ℝ)
    (cell12890 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · norm_num [cell12890]
  · have h := gap_lower (n := 12890) (a := (82729574468879 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114437915571 / 50000000000000 : ℝ))
      (E := (cell12890 ⟨39, by decide⟩).energy) (xi := (329036678495491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12890 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12890]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12890])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12890) (a := (82729574468879 / 100000000000000 : ℝ)) (b := (159770170099 / 100000000000000 : ℝ)) (q := (1114437915571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12890])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12890]

theorem cert12891_20 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83379533054967 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228682685467 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨20, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83379533054967 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228682685467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_21 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83345108777973 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114343372027 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨21, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83345108777973 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114343372027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_22 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41655354329253 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228690743937 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨22, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41655354329253 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228690743937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_23 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41638166331923 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114347373433 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨23, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41638166331923 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114347373433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_24 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (20810495190361 / 25000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (557174689013 / 25000000000000 : ℝ))
      (E := (cell12891 ⟨24, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (20810495190361 / 25000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (557174689013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_25 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (16641530583783 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (445740543213 / 20000000000000 : ℝ))
      (E := (cell12891 ⟨25, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (16641530583783 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (445740543213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_26 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83173349104043 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114353373227 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨26, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83173349104043 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114353373227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_27 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83139069284773 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228710732883 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨27, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83139069284773 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228710732883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_28 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83104813429217 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (44574294721 / 2000000000000 : ℝ))
      (E := (cell12891 ⟨28, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83104813429217 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (44574294721 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_29 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (5191911344103 / 6250000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (278589844751 / 12500000000000 : ℝ))
      (E := (cell12891 ⟨29, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (5191911344103 / 6250000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (278589844751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_30 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (83036373482501 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228722742049 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨30, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (83036373482501 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228722742049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_31 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41501094664187 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (8914906993 / 400000000000 : ℝ))
      (E := (cell12891 ⟨31, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41501094664187 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (8914906993 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_32 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41484014506011 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (111436538899 / 5000000000000 : ℝ))
      (E := (cell12891 ⟨32, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41484014506011 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (111436538899 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_33 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (2073347312559 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228734773777 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨33, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (2073347312559 / 2500000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228734773777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_34 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82899779768461 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228738795111 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨34, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82899779768461 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228738795111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_35 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (16573138155911 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114371392011 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨35, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (16573138155911 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114371392011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_36 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82831625505027 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114373399789 / 50000000000000 : ℝ))
      (E := (cell12891 ⟨36, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82831625505027 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (1114373399789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_37 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (82797583914419 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (89150031333 / 4000000000000 : ℝ))
      (E := (cell12891 ⟨37, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (82797583914419 / 100000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (89150031333 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_38 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (41381782988713 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228754793931 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨38, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (41381782988713 / 50000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228754793931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12891_39 : CellCertificate 12891 (110178816757517 / 1250000000000000 : ℝ) (814689565566723 / 500000000000000000 : ℝ) (329010550204659 / 10000000000000000 : ℝ)
    (cell12891 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · norm_num [cell12891]
  · have h := gap_lower (n := 12891) (a := (16545914332779 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228758831197 / 100000000000000 : ℝ))
      (E := (cell12891 ⟨39, by decide⟩).energy) (xi := (329010550204659 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12891 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12891]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12891])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12891) (a := (16545914332779 / 20000000000000 : ℝ)) (b := (159757629583 / 100000000000000 : ℝ)) (q := (2228758831197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12891])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12891]

theorem cert12892_20 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (2605610142019 / 3125000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114282872841 / 50000000000000 : ℝ))
      (E := (cell12892 ⟨20, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (2605610142019 / 3125000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114282872841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_21 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (8334510057171 / 10000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (17828557891 / 800000000000 : ℝ))
      (E := (cell12892 ⟨21, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (8334510057171 / 10000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (17828557891 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_22 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (20827675188979 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228573785703 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨22, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (20827675188979 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228573785703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_23 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83276325064507 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228577780453 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨23, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83276325064507 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228577780453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_24 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41620986732467 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228581782159 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨24, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41620986732467 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228581782159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_25 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83207645924813 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228585793801 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨25, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83207645924813 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228585793801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_26 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (10396667801491 / 12500000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (278573719961 / 12500000000000 : ℝ))
      (E := (cell12892 ⟨26, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (10396667801491 / 12500000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (278573719961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_27 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (83139062894227 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (139287112449 / 6250000000000 : ℝ))
      (E := (cell12892 ⟨27, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (83139062894227 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (139287112449 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_28 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41552403669911 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228597797673 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨28, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41552403669911 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228597797673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_29 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41535287858493 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228601815647 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨29, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41535287858493 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228601815647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_30 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (16607273598831 / 20000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557151449099 / 25000000000000 : ℝ))
      (E := (cell12892 ⟨30, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (16607273598831 / 20000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557151449099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_31 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (10375273017491 / 12500000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114304899999 / 50000000000000 : ℝ))
      (E := (cell12892 ⟨31, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (10375273017491 / 12500000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (1114304899999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_32 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82968024123061 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228613827819 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨32, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82968024123061 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228613827819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_33 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (8293388791247 / 10000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557154455599 / 25000000000000 : ℝ))
      (E := (cell12892 ⟨33, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (8293388791247 / 10000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (557154455599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_34 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (20724943869307 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (348222163 / 15625000000 : ℝ))
      (E := (cell12892 ⟨34, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (20724943869307 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (348222163 / 15625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_35 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (41432843393283 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (222862583227 / 10000000000000 : ℝ))
      (E := (cell12892 ⟨35, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (41432843393283 / 50000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (222862583227 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_36 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82831621809871 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (69644682771 / 3125000000000 : ℝ))
      (E := (cell12892 ⟨36, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82831621809871 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (69644682771 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_37 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (20699395129171 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (69644807311 / 3125000000000 : ℝ))
      (E := (cell12892 ⟨37, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (20699395129171 / 25000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (69644807311 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_38 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82763562876701 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228637846779 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨38, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82763562876701 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228637846779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12892_39 : CellCertificate 12892 (881403388217793 / 10000000000000000 : ℝ) (1629252703358109 / 1000000000000000000 : ℝ) (164492213053009 / 5000000000000000 : ℝ)
    (cell12892 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · norm_num [cell12892]
  · have h := gap_lower (n := 12892) (a := (82729568859771 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228641886949 / 100000000000000 : ℝ))
      (E := (cell12892 ⟨39, by decide⟩).energy) (xi := (164492213053009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12892 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12892]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12892])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12892) (a := (82729568859771 / 100000000000000 : ℝ)) (b := (79872545523 / 50000000000000 : ℝ)) (q := (2228641886949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12892])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12892]

theorem cert12893_20 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (8337951603579 / 10000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (557112200539 / 25000000000000 : ℝ))
      (E := (cell12893 ⟨20, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (8337951603579 / 10000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (557112200539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_21 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (10418136545869 / 12500000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (69639151301 / 3125000000000 : ℝ))
      (E := (cell12893 ⟨21, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (10418136545869 / 12500000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (69639151301 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_22 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (16662138570959 / 20000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228456823801 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨22, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (16662138570959 / 20000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228456823801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_23 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (416381587333 / 500000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228460810411 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨23, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (416381587333 / 500000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228460810411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_24 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (4162098308491 / 5000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (278558107883 / 12500000000000 : ℝ))
      (E := (cell12893 ⟨24, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (4162098308491 / 5000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (278558107883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_25 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83207638932071 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114234433991 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨25, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83207638932071 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114234433991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_26 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (41586667860569 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (6963977587 / 312500000000 : ℝ))
      (E := (cell12893 ⟨26, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (41586667860569 / 50000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (6963977587 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_27 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (8313905650497 / 10000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114238431001 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨27, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (8313905650497 / 10000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114238431001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_28 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83104801251679 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228480855851 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨28, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83104801251679 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228480855851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_29 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (4153528496477 / 5000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114242434939 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨29, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (4153528496477 / 5000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114242434939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_30 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (8303636250699 / 10000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (557122211843 / 25000000000000 : ℝ))
      (E := (cell12893 ⟨30, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (8303636250699 / 10000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (557122211843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_31 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (83002178952627 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445698581393 / 20000000000000 : ℝ))
      (E := (cell12893 ⟨31, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (83002178952627 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445698581393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_32 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82968019235209 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228496874359 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨32, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82968019235209 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228496874359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_33 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82933883323653 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114250433877 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨33, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82933883323653 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114250433877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_34 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82899771187033 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (8705097219 / 390625000000 : ℝ))
      (E := (cell12893 ⟨34, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82899771187033 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (8705097219 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_35 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82865682794579 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228508935977 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨35, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82865682794579 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228508935977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_36 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82831618115681 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228512894613 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨36, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82831618115681 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228512894613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_37 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82797577119879 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228516940159 / 100000000000000 : ℝ))
      (E := (cell12893 ⟨37, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82797577119879 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (2228516940159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_38 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82763559776871 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445704191053 / 20000000000000 : ℝ))
      (E := (cell12893 ⟨38, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82763559776871 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (445704191053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12893_39 : CellCertificate 12893 (440688123206329 / 5000000000000000 : ℝ) (162912629520097 / 100000000000000000 : ℝ) (328958306198489 / 10000000000000000 : ℝ)
    (cell12893 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · norm_num [cell12893]
  · have h := gap_lower (n := 12893) (a := (82729566056507 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114262469829 / 50000000000000 : ℝ))
      (E := (cell12893 ⟨39, by decide⟩).energy) (xi := (328958306198489 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12893 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12893]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12893])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12893) (a := (82729566056507 / 100000000000000 : ℝ)) (b := (159732554487 / 100000000000000 : ℝ)) (q := (1114262469829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12893])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12893]

theorem cert12894_20 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83379507528513 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445666382637 / 20000000000000 : ℝ))
      (E := (cell12894 ⟨20, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83379507528513 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445666382637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_21 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (833450841637 / 1000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (139270996449 / 6250000000000 : ℝ))
      (E := (cell12894 ⟨21, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (833450841637 / 1000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (139270996449 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_22 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41655342477571 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228339916577 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨22, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41655342477571 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228339916577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_23 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41638154935063 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228343953473 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨23, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41638154935063 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228343953473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_24 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41620979438051 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (17826783523 / 800000000000 : ℝ))
      (E := (cell12894 ⟨24, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41620979438051 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (17826783523 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_25 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83207631940689 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114175969303 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨25, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83207631940689 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114175969303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_26 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (10396666128959 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (222835595091 / 10000000000000 : ℝ))
      (E := (cell12894 ⟨26, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (10396666128959 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (222835595091 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_27 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (83139050117001 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114179989899 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨27, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (83139050117001 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114179989899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_28 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20776198791197 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (557090992267 / 25000000000000 : ℝ))
      (E := (cell12894 ⟨28, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20776198791197 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (557090992267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_29 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (8307056414331 / 10000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228367979207 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨29, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (8307056414331 / 10000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228367979207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_30 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (20759089255251 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228371953507 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨30, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (20759089255251 / 25000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228371953507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_31 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (8300217376647 / 10000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114187976021 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨31, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (8300217376647 / 10000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114187976021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_32 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41484007174233 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228379976177 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨32, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41484007174233 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228379976177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_33 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (82933878735909 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (44567679369 / 2000000000000 : ℝ))
      (E := (cell12894 ⟨33, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (82933878735909 / 100000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (44567679369 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_34 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41449883448937 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228387988327 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨34, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41449883448937 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228387988327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_35 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41432839401797 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114195988923 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨35, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41432839401797 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114195988923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_36 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (10353951802807 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114197998037 / 50000000000000 : ℝ))
      (E := (cell12894 ⟨36, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (10353951802807 / 12500000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (1114197998037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_37 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (16559514744801 / 20000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228400043249 / 100000000000000 : ℝ))
      (E := (cell12894 ⟨37, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (16559514744801 / 20000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (2228400043249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_38 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (5172722292371 / 6250000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (69637625061 / 3125000000000 : ℝ))
      (E := (cell12894 ⟨38, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (5172722292371 / 6250000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (69637625061 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12894_39 : CellCertificate 12894 (176269821728757 / 2000000000000000 : ℝ) (1628999906657463 / 1000000000000000000 : ℝ) (328932190480991 / 10000000000000000 : ℝ)
    (cell12894 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · norm_num [cell12894]
  · have h := gap_lower (n := 12894) (a := (41364781627051 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445681609613 / 20000000000000 : ℝ))
      (E := (cell12894 ⟨39, by decide⟩).energy) (xi := (328932190480991 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12894 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12894]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12894])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12894) (a := (41364781627051 / 50000000000000 : ℝ)) (b := (159720019907 / 100000000000000 : ℝ)) (q := (445681609613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12894])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12894]

theorem cert12895_20 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83379499022777 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114107510237 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨20, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83379499022777 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114107510237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_21 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83345075961951 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114109520517 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨21, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83345075961951 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114109520517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_22 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (41655338528479 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228223064029 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨22, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (41655338528479 / 50000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228223064029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_23 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20819075568771 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228227034539 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨23, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20819075568771 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228227034539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_24 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (4162097579189 / 5000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114115536243 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨24, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (4162097579189 / 5000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114115536243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_25 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83207624950667 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222823506409 / 10000000000000 : ℝ))
      (E := (cell12895 ⟨25, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83207624950667 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222823506409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_26 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (8317332234353 / 10000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114119535231 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨26, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (8317332234353 / 10000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114119535231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_27 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83139043730319 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114121547057 / 50000000000000 : ℝ))
      (E := (cell12895 ⟨27, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83139043730319 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (1114121547057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_28 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83104789079149 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228247078841 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨28, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83104789079149 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228247078841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_29 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (10383819794787 / 12500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222825108513 / 10000000000000 : ℝ))
      (E := (cell12895 ⟨29, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (10383819794787 / 12500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (222825108513 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_30 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83036351536199 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228255114803 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨30, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83036351536199 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228255114803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_31 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (83002168581457 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (445651822179 / 20000000000000 : ℝ))
      (E := (cell12895 ⟨31, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (83002168581457 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (445651822179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_32 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (8296800946283 / 10000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228263133279 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨32, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (8296800946283 / 10000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228263133279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_33 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82933874149237 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (278533390561 / 12500000000000 : ℝ))
      (E := (cell12895 ⟨33, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82933874149237 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (278533390561 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_34 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (10362470326219 / 12500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (278533892999 / 12500000000000 : ℝ))
      (E := (cell12895 ⟨34, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (10362470326219 / 12500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (278533892999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_35 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82865674813609 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228275133827 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨35, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82865674813609 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228275133827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_36 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (82831610730197 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (69633723533 / 3125000000000 : ℝ))
      (E := (cell12895 ⟨36, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (82831610730197 / 100000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (69633723533 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_37 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (4139878516453 / 5000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (89131325729 / 4000000000000 : ℝ))
      (E := (cell12895 ⟨37, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (4139878516453 / 5000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (89131325729 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_38 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (10345444197487 / 12500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228287162999 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨38, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (10345444197487 / 12500000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228287162999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12895_39 : CellCertificate 12895 (881321974910231 / 10000000000000000 : ℝ) (814436768861511 / 500000000000000000 : ℝ) (82226519738111 / 2500000000000000 : ℝ)
    (cell12895 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · norm_num [cell12895]
  · have h := gap_lower (n := 12895) (a := (20682390113139 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228291153431 / 100000000000000 : ℝ))
      (E := (cell12895 ⟨39, by decide⟩).energy) (xi := (82226519738111 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12895 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12895]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12895])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12895) (a := (20682390113139 / 25000000000000 : ℝ)) (b := (19963435913 / 12500000000000 : ℝ)) (q := (2228291153431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12895])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12895]

theorem cert12896_20 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41689745259291 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228098182321 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨20, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41689745259291 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228098182321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_21 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83345067761707 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114051096751 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨21, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83345067761707 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114051096751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_22 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41655334580121 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114053103909 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨22, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41655334580121 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114053103909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_23 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83276294681473 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (278513778589 / 12500000000000 : ℝ))
      (E := (cell12896 ⟨23, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83276294681473 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (278513778589 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_24 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83241944292853 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228114201007 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨24, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83241944292853 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228114201007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_25 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (20801904490501 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228118186021 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨25, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (20801904490501 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228118186021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_26 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (8317331565671 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228122244937 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨26, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (8317331565671 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228122244937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_27 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (20784759336231 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228126204951 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨27, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (20784759336231 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228126204951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_28 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (2077619574869 / 2500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (278516280457 / 12500000000000 : ℝ))
      (E := (cell12896 ⟨28, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (2077619574869 / 2500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (278516280457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_29 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (83070552574497 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445626849231 / 20000000000000 : ℝ))
      (E := (cell12896 ⟨29, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (83070552574497 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445626849231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_30 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (20759086513143 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228138214199 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨30, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (20759086513143 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228138214199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_31 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (20750540849397 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445628453283 / 20000000000000 : ℝ))
      (E := (cell12896 ⟨31, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (20750540849397 / 25000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (445628453283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_32 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82968004578303 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (278518278563 / 12500000000000 : ℝ))
      (E := (cell12896 ⟨32, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82968004578303 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (278518278563 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_33 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82933869563637 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228150277267 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨33, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82933869563637 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228150277267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_34 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (82899758322667 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (139259639863 / 6250000000000 : ℝ))
      (E := (cell12896 ⟨34, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (82899758322667 / 100000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (139259639863 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_35 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41432835412313 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228158286619 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨35, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41432835412313 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228158286619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_36 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (10353950879863 / 12500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (278520288361 / 12500000000000 : ℝ))
      (E := (cell12896 ⟨36, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (10353950879863 / 12500000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (278520288361 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_37 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (41398783467523 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114083149391 / 50000000000000 : ℝ))
      (E := (cell12896 ⟨37, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (41398783467523 / 50000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (1114083149391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_38 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (331054201931 / 400000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228170320969 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨38, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (331054201931 / 400000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228170320969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12896_39 : CellCertificate 12896 (881294845211053 / 10000000000000000 : ℝ) (325749437678617 / 200000000000000000 : ℝ) (32887997161177 / 1000000000000000 : ℝ)
    (cell12896 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · norm_num [cell12896]
  · have h := gap_lower (n := 12896) (a := (8272955765187 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228174314497 / 100000000000000 : ℝ))
      (E := (cell12896 ⟨39, by decide⟩).energy) (xi := (32887997161177 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12896 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12896]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12896])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12896) (a := (8272955765187 / 10000000000000 : ℝ)) (b := (79847478339 / 50000000000000 : ℝ)) (q := (2228174314497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12896])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12896]

theorem cert12897_20 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41689741007963 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (222798134043 / 10000000000000 : ℝ))
      (E := (cell12897 ⟨20, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41689741007963 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (222798134043 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_21 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41672529781483 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (222798534227 / 10000000000000 : ℝ))
      (E := (cell12897 ⟨21, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41672529781483 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (222798534227 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_22 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83310661264993 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1113994673971 / 50000000000000 : ℝ))
      (E := (cell12897 ⟨22, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83310661264993 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1113994673971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_23 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83276287089293 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227993360891 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨23, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83276287089293 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2227993360891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_24 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83241937003321 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (278499673041 / 12500000000000 : ℝ))
      (E := (cell12897 ⟨24, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83241937003321 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (278499673041 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_25 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83207610974699 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228001362813 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨25, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83207610974699 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228001362813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_26 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83173308971213 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445601083179 / 20000000000000 : ℝ))
      (E := (cell12897 ⟨26, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83173308971213 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (445601083179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_27 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (5196189435051 / 6250000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (222800942923 / 10000000000000 : ℝ))
      (E := (cell12897 ⟨27, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (5196189435051 / 6250000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (222800942923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_28 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83104776911623 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557003351257 / 25000000000000 : ℝ))
      (E := (cell12897 ⟨28, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83104776911623 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557003351257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_29 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (10383818348989 / 12500000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (89120696151 / 4000000000000 : ℝ))
      (E := (cell12897 ⟨29, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (10383818348989 / 12500000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (89120696151 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_30 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (664290724561 / 800000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (278502678411 / 12500000000000 : ℝ))
      (E := (cell12897 ⟨30, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (664290724561 / 800000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (278502678411 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_31 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (83002158214861 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557006354651 / 25000000000000 : ℝ))
      (E := (cell12897 ⟨31, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (83002158214861 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557006354651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_32 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82967999694883 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (278503679699 / 12500000000000 : ℝ))
      (E := (cell12897 ⟨32, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82967999694883 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (278503679699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_33 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82933864979109 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228033426787 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨33, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82933864979109 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228033426787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_34 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41449877018309 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557009361413 / 25000000000000 : ℝ))
      (E := (cell12897 ⟨34, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41449877018309 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (557009361413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_35 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82865666836643 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114020718113 / 50000000000000 : ℝ))
      (E := (cell12897 ⟨35, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82865666836643 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114020718113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_36 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (2588487604643 / 3125000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228045457569 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨36, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (2588487604643 / 3125000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228045457569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_37 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82797563541961 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114024725613 / 50000000000000 : ℝ))
      (E := (cell12897 ⟨37, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82797563541961 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (1114024725613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_38 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (82763547386499 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (111402673793 / 5000000000000 : ℝ))
      (E := (cell12897 ⟨38, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (82763547386499 / 100000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (111402673793 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12897_39 : CellCertificate 12897 (440633859772653 / 5000000000000000 : ℝ) (162862085866309 / 100000000000000000 : ℝ) (32885386845789 / 1000000000000000 : ℝ)
    (cell12897 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · norm_num [cell12897]
  · have h := gap_lower (n := 12897) (a := (41364777426021 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228057472523 / 100000000000000 : ℝ))
      (E := (cell12897 ⟨39, by decide⟩).energy) (xi := (32885386845789 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12897 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12897]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12897])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12897) (a := (41364777426021 / 50000000000000 : ℝ)) (b := (159682428029 / 100000000000000 : ℝ)) (q := (2228057472523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12897])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12897]

theorem cert12898_20 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83379473514811 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113932276549 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨20, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83379473514811 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113932276549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_21 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83345051365729 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227868545657 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨21, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83345051365729 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227868545657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_22 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83310653371211 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227872601091 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨22, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83310653371211 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227872601091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_23 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (5204767468659 / 6250000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (111393830309 / 5000000000000 : ℝ))
      (E := (cell12898 ⟨23, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (5204767468659 / 6250000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (111393830309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_24 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (16648385943037 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (111394028203 / 5000000000000 : ℝ))
      (E := (cell12898 ⟨24, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (16648385943037 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (111394028203 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_25 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41603801994377 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227884594467 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨25, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41603801994377 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227884594467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_26 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83173302287039 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113944291669 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨26, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83173302287039 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113944291669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_27 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (16627804915599 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (222789259157 / 10000000000000 : ℝ))
      (E := (cell12898 ⟨27, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (16627804915599 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (222789259157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_28 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (10388096353717 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445579324289 / 20000000000000 : ℝ))
      (E := (cell12898 ⟨28, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (10388096353717 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445579324289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_29 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (83070541010543 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113950308249 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨29, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (83070541010543 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113950308249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_30 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (10379541886107 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227904637011 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨30, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (10379541886107 / 12500000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227904637011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_31 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (41501076516639 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (69622144563 / 3125000000000 : ℝ))
      (E := (cell12898 ⟨31, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (41501076516639 / 50000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (69622144563 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_32 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (8296799481257 / 10000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445582528677 / 20000000000000 : ℝ))
      (E := (cell12898 ⟨32, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (8296799481257 / 10000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445582528677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_33 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (82933860395653 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (44558332633 / 2000000000000 : ℝ))
      (E := (cell12898 ⟨33, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (82933860395653 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (44558332633 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_34 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (20724937437901 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556980162569 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨34, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (20724937437901 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556980162569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_35 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (4143283142483 / 5000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227924641297 / 100000000000000 : ℝ))
      (E := (cell12898 ⟨35, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (4143283142483 / 5000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (2227924641297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_36 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (20707899914803 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (89117146551 / 4000000000000 : ℝ))
      (E := (cell12898 ⟨36, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (20707899914803 / 25000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (89117146551 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_37 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (16559512029961 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113966329627 / 50000000000000 : ℝ))
      (E := (cell12898 ⟨37, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (16559512029961 / 20000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (1113966329627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_38 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (82763544291141 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445587337279 / 20000000000000 : ℝ))
      (E := (cell12898 ⟨38, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (82763544291141 / 100000000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (445587337279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12898_39 : CellCertificate 12898 (55077537369503 / 625000000000000 : ℝ) (1628494548528477 / 1000000000000000000 : ℝ) (13153110779589 / 400000000000000 : ℝ)
    (cell12898 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · norm_num [cell12898]
  · have h := gap_lower (n := 12898) (a := (5170597003317 / 6250000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556985171563 / 25000000000000 : ℝ))
      (E := (cell12898 ⟨39, by decide⟩).energy) (xi := (13153110779589 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12898 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12898]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12898])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12898) (a := (5170597003317 / 6250000000000 : ℝ)) (b := (39917475339 / 25000000000000 : ℝ)) (q := (556985171563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12898])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12898]

theorem cert12899_20 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41689732507617 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227747820329 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨20, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41689732507617 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227747820329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_21 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41672521584997 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556937950917 / 25000000000000 : ℝ))
      (E := (cell12899 ⟨21, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41672521584997 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556937950917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_22 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (5206915342431 / 6250000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445551158447 / 20000000000000 : ℝ))
      (E := (cell12899 ⟨22, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (5206915342431 / 6250000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445551158447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_23 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41638135954613 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556939947369 / 25000000000000 : ℝ))
      (E := (cell12899 ⟨23, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41638135954613 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556939947369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_24 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41620961214221 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556940949649 / 25000000000000 : ℝ))
      (E := (cell12899 ⟨24, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41620961214221 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556940949649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_25 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41603798502083 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556941955643 / 25000000000000 : ℝ))
      (E := (cell12899 ⟨25, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41603798502083 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (556941955643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_26 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83173295604187 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113885902853 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨26, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83173295604187 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113885902853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_27 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83139018196459 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (17404498507 / 781250000000 : ℝ))
      (E := (cell12899 ⟨27, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83139018196459 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (17404498507 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_28 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (83104764749099 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227779834421 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨28, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (83104764749099 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227779834421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_29 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (20767633807597 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113891912909 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨29, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (20767633807597 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113891912909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_30 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41518164804383 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227787843367 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨30, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41518164804383 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227787843367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_31 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41501073926419 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227791830099 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨31, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41501073926419 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227791830099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_32 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (20741997482841 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445559169177 / 20000000000000 : ℝ))
      (E := (cell12899 ⟨32, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (20741997482841 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (445559169177 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_33 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (20733463953317 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227799891859 / 100000000000000 : ℝ))
      (E := (cell12899 ⟨33, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (20733463953317 / 25000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (2227799891859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_34 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82899745467627 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113901925839 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨34, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82899745467627 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113901925839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_35 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (41432829431839 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (278475987729 / 12500000000000 : ℝ))
      (E := (cell12899 ⟨35, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (41432829431839 / 50000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (278475987729 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_36 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82831595970813 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113905933417 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨36, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82831595970813 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113905933417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_37 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82797556758579 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (222781586417 / 10000000000000 : ℝ))
      (E := (cell12899 ⟨37, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82797556758579 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (222781586417 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_38 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82763541196677 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (69619371683 / 3125000000000 : ℝ))
      (E := (cell12899 ⟨38, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82763541196677 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (69619371683 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

theorem cert12899_39 : CellCertificate 12899 (13768960629849 / 156250000000000 : ℝ) (1628368257984687 / 1000000000000000000 : ℝ) (164400837353099 / 5000000000000000 : ℝ)
    (cell12899 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · norm_num [cell12899]
  · have h := gap_lower (n := 12899) (a := (82729549254961 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113911948471 / 50000000000000 : ℝ))
      (E := (cell12899 ⟨39, by decide⟩).energy) (xi := (164400837353099 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12899 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12899]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12899])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12899) (a := (82729549254961 / 100000000000000 : ℝ)) (b := (79828688329 / 50000000000000 : ℝ)) (q := (1113911948471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12899])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12899]

end BstLean.Part268
