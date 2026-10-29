import BstLean.Part268CellShard3Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12425_20 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41691836704803 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286833010081 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨20, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41691836704803 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286833010081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_21 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (3333964133593 / 4000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (142927314731 / 6250000000000 : ℝ))
      (E := (cell12425 ⟨21, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (3333964133593 / 4000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (142927314731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_22 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83314557630959 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285855126573 / 12500000000000 : ℝ))
      (E := (cell12425 ⟨22, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83314557630959 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285855126573 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_23 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (2082000906247 / 2500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286845003259 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨23, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (2082000906247 / 2500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286845003259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_24 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83245539163633 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (1143424505873 / 50000000000000 : ℝ))
      (E := (cell12425 ⟨24, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83245539163633 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (1143424505873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_25 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (8321106633943 / 10000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286853041833 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨25, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (8321106633943 / 10000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286853041833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_26 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (5198538609041 / 6250000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286857038677 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨26, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (5198538609041 / 6250000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286857038677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_27 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83142193346859 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285857625691 / 12500000000000 : ℝ))
      (E := (cell12425 ⟨27, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83142193346859 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285857625691 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_28 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (16621558622751 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (457373000767 / 20000000000000 : ℝ))
      (E := (cell12425 ⟨28, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (16621558622751 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (457373000767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_29 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (20768354253307 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (457373807289 / 20000000000000 : ℝ))
      (E := (cell12425 ⟨29, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (20768354253307 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (457373807289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_30 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41519532506661 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228687298901 / 10000000000000 : ℝ))
      (E := (cell12425 ⟨30, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41519532506661 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228687298901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_31 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83004737082249 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571719245197 / 25000000000000 : ℝ))
      (E := (cell12425 ⟨31, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83004737082249 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571719245197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_32 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (4148521659419 / 5000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286881013937 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨32, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (4148521659419 / 5000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286881013937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_33 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (331744613201 / 400000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285860621659 / 12500000000000 : ℝ))
      (E := (cell12425 ⟨33, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (331744613201 / 400000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285860621659 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_34 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (10362737173319 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228688897751 / 10000000000000 : ℝ))
      (E := (cell12425 ⟨34, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (10362737173319 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228688897751 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_35 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (82867665416141 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286892969519 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨35, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (82867665416141 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286892969519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_36 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (20708364339507 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286897009099 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨36, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (20708364339507 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286897009099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_37 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (16559854636277 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228690097997 / 10000000000000 : ℝ))
      (E := (cell12425 ⟨37, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (16559854636277 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228690097997 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_38 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41382556427769 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571726250033 / 25000000000000 : ℝ))
      (E := (cell12425 ⟨38, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41382556427769 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571726250033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_39 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (5170686021873 / 6250000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (114345450573 / 5000000000000 : ℝ))
      (E := (cell12425 ⟨39, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (5170686021873 / 6250000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (114345450573 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12426_20 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41691832068403 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (285837271733 / 12500000000000 : ℝ))
      (E := (cell12426 ⟨20, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41691832068403 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (285837271733 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_21 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83349094388889 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143351081879 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨21, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83349094388889 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143351081879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_22 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83314549001437 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286706163947 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨22, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83314549001437 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286706163947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_23 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (20820006985331 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286710120373 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨23, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (20820006985331 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286710120373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_24 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41622765587797 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286714153679 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨24, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41622765587797 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286714153679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_25 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41605529335731 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143359075493 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨25, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41605529335731 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143359075493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_26 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83176610396311 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286722115773 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨26, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83176610396311 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286722115773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_27 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (20785546579423 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143363054851 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨27, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (20785546579423 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143363054851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_28 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83107786403323 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286730135853 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨28, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83107786403323 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286730135853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_29 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (16614682124217 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143367069307 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨29, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (16614682124217 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143367069307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_30 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83039058939027 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (228673812053 / 10000000000000 : ℝ))
      (E := (cell12426 ⟨30, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83039058939027 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (228673812053 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_31 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83004731325359 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143371071213 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨31, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83004731325359 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143371071213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_32 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41485213874227 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (142921630587 / 6250000000000 : ℝ))
      (E := (cell12426 ⟨32, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41485213874227 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (142921630587 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_33 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82936148176847 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (893261773 / 39062500000 : ℝ))
      (E := (cell12426 ⟨33, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82936148176847 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (893261773 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_34 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41450946289617 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286754116921 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨34, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41450946289617 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286754116921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_35 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82867660924469 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286758083447 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨35, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82867660924469 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286758083447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_36 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (20708363295391 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286762098259 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨36, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (20708363295391 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286762098259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_37 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (20699817329923 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (571691525931 / 25000000000000 : ℝ))
      (E := (cell12426 ⟨37, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (20699817329923 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (571691525931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_38 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82765109308179 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (457354020113 / 20000000000000 : ℝ))
      (E := (cell12426 ⟨38, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82765109308179 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (457354020113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_39 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82730973116509 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286774089283 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨39, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82730973116509 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286774089283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12427_20 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83383654865741 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286563333397 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨20, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83383654865741 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286563333397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_21 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83349085439649 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286567345883 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨21, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83349085439649 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286567345883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_22 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83314540373571 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286571311141 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨22, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83314540373571 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286571311141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_23 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83280019634383 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (14291095573 / 625000000000 : ℝ))
      (E := (cell12427 ⟨23, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83280019634383 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (14291095573 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_24 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83245523189131 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (91463171661 / 4000000000000 : ℝ))
      (E := (cell12427 ⟨24, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83245523189131 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (91463171661 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_25 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83211051005029 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286583314461 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨25, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83211051005029 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286583314461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_26 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83176603049463 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143293652823 / 50000000000000 : ℝ))
      (E := (cell12427 ⟨26, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83176603049463 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143293652823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_27 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41571089644991 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286591326741 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨27, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41571089644991 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286591326741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_28 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83107779694307 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143297661193 / 50000000000000 : ℝ))
      (E := (cell12427 ⟨28, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83107779694307 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143297661193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_29 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (1038417552879 / 1250000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (3572811399 / 156250000000 : ℝ))
      (E := (cell12427 ⟨29, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (1038417552879 / 1250000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (3572811399 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_30 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (8303905286607 / 10000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286603306693 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨30, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (8303905286607 / 10000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286603306693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_31 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83004725569767 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143303650131 / 50000000000000 : ℝ))
      (E := (cell12427 ⟨31, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83004725569767 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143303650131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_32 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (20742605577447 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286611278149 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨32, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (20742605577447 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286611278149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_33 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (16587228610933 / 20000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143307650383 / 50000000000000 : ℝ))
      (E := (cell12427 ⟨33, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (16587228610933 / 20000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143307650383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_34 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82901887773097 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (228661931123 / 10000000000000 : ℝ))
      (E := (cell12427 ⟨34, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82901887773097 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (228661931123 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_35 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41433828216969 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (114331165547 / 5000000000000 : ℝ))
      (E := (cell12427 ⟨35, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41433828216969 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (114331165547 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_36 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82833449006203 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286627301069 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨36, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82833449006203 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286627301069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_37 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82799265459063 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457326256513 / 20000000000000 : ℝ))
      (E := (cell12427 ⟨37, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82799265459063 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457326256513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_38 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41382552880923 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286635256149 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨38, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41382552880923 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286635256149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_39 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (20682742471009 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143319640509 / 50000000000000 : ℝ))
      (E := (cell12427 ⟨39, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (20682742471009 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143319640509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12428_20 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (8338364559641 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286428546931 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨20, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (8338364559641 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286428546931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_21 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (83349076492103 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (11432162619 / 500000000000 : ℝ))
      (E := (cell12428 ⟨21, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (83349076492103 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (11432162619 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_22 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (520715823421 / 625000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286436570761 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨22, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (520715823421 / 625000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286436570761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_23 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41640005664529 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286440517181 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨23, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41640005664529 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286440517181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_24 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (83245515204243 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286444541973 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨24, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (83245515204243 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286444541973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_25 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (20802760835033 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286448532259 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨25, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (20802760835033 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286448532259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_26 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (8317659570411 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143226274953 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨26, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (8317659570411 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143226274953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_27 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (83142172263729 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457291307963 / 20000000000000 : ℝ))
      (E := (cell12428 ⟨27, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (83142172263729 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457291307963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_28 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (20776943246677 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571615126249 / 25000000000000 : ℝ))
      (E := (cell12428 ⟨28, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (20776943246677 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571615126249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_29 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (83073397840933 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457292901337 / 20000000000000 : ℝ))
      (E := (cell12428 ⟨29, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (83073397840933 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457292901337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_30 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (83039046794451 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286468547499 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨30, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (83039046794451 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286468547499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_31 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (3320188792619 / 4000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571618128201 / 25000000000000 : ℝ))
      (E := (cell12428 ⟨31, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (3320188792619 / 4000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571618128201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_32 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (4148520843619 / 5000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286476521677 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨32, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (4148520843619 / 5000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286476521677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_33 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (10367017241713 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457296103497 / 20000000000000 : ℝ))
      (E := (cell12428 ⟨33, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (10367017241713 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457296103497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_34 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82901882968141 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286484501857 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨34, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82901882968141 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286484501857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_35 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (1657353038891 / 2000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286488534791 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨35, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (1657353038891 / 2000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286488534791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_36 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (10354180603993 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286492500279 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨36, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (10354180603993 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286492500279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_37 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82799261599497 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457299303299 / 20000000000000 : ℝ))
      (E := (cell12428 ⟨37, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82799261599497 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457299303299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_38 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82765102216537 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143250262779 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨38, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82765102216537 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143250262779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_39 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82730966652549 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (71453266499 / 3125000000000 : ℝ))
      (E := (cell12428 ⟨39, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82730966652549 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (71453266499 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12429_20 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (41691818164407 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143146907233 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨20, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (41691818164407 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143146907233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_21 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83349067546251 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286297814057 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨21, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83349067546251 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286297814057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_22 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83314523122803 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457260365243 / 20000000000000 : ℝ))
      (E := (cell12429 ⟨22, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83314523122803 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457260365243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_23 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83280003025347 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286305855197 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨23, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83280003025347 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286305855197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_24 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83245507220931 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (57157746167 / 2500000000000 : ℝ))
      (E := (cell12429 ⟨24, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83245507220931 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (57157746167 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_25 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83211035676771 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143156902189 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨25, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83211035676771 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143156902189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_26 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83176588360253 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286317848553 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨26, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83176588360253 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286317848553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_27 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20785541309733 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (114316090367 / 5000000000000 : ℝ))
      (E := (cell12429 ⟨27, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20785541309733 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (114316090367 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_28 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (41553883140263 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143162900279 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨28, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (41553883140263 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143162900279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_29 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (41536695726461 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286329831051 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨29, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (41536695726461 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286329831051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_30 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83039040724169 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286333784463 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨30, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83039040724169 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286333784463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_31 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (1037558925781 / 1250000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286337838563 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨31, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (1037558925781 / 1250000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286337838563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_32 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (10371301429529 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (91453672799 / 4000000000000 : ℝ))
      (E := (cell12429 ⟨32, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (10371301429529 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (91453672799 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_33 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (41468066406981 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286345789039 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨33, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (41468066406981 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286345789039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_34 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (41450939082183 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286349805961 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨34, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (41450939082183 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286349805961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_35 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82867647456303 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (571588453401 / 25000000000000 : ℝ))
      (E := (cell12429 ⟨35, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82867647456303 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (571588453401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_36 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20708360164697 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (114317890657 / 5000000000000 : ℝ))
      (E := (cell12429 ⟨36, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20708360164697 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (114317890657 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_37 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (16559851548199 / 20000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143180902757 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨37, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (16559851548199 / 20000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143180902757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_38 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82765098672253 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286365791447 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨38, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82765098672253 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286365791447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_39 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (2585342606939 / 3125000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (571592442859 / 25000000000000 : ℝ))
      (E := (cell12429 ⟨39, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (2585342606939 / 3125000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (571592442859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12430_20 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (10422953382869 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (457231838851 / 20000000000000 : ℝ))
      (E := (cell12430 ⟨20, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (10422953382869 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (457231838851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_21 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41674529301047 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143081579191 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨21, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41674529301047 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143081579191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_22 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (83314514499901 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286167194099 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨22, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (83314514499901 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286167194099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_23 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (83279994723251 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286171189089 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨23, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (83279994723251 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286171189089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_24 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (10405687404899 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (457235029461 / 20000000000000 : ℝ))
      (E := (cell12430 ⟨24, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (10405687404899 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (457235029461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_25 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (2600344625467 / 3125000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286179189193 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨25, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (2600344625467 / 3125000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286179189193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_26 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (83176581017891 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143091571599 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨26, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (83176581017891 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143091571599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_27 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (8314215821559 / 10000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (285773398467 / 12500000000000 : ℝ))
      (E := (cell12430 ⟨27, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (8314215821559 / 10000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (285773398467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_28 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (1038846994697 / 1250000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286191150639 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨28, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (1038846994697 / 1250000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286191150639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_29 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (5192086566643 / 6250000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286195151537 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨29, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (5192086566643 / 6250000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286195151537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_30 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (3321561386209 / 4000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286199134557 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨30, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (3321561386209 / 4000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286199134557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_31 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (324237141839 / 390625000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286203160521 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨31, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (324237141839 / 390625000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286203160521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_32 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82970406001343 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286207173047 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨32, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82970406001343 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286207173047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_33 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82936127695439 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286211173987 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨33, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82936127695439 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286211173987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_34 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82901873361771 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286215164967 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨34, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82901873361771 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286215164967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_35 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82867642969197 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143109573691 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨35, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82867642969197 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143109573691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_36 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41416718243367 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286223122403 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨36, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41416718243367 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286223122403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_37 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (20699813470889 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (285778393703 / 12500000000000 : ℝ))
      (E := (cell12430 ⟨37, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (20699813470889 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (285778393703 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_38 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82765095128993 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571557792791 / 25000000000000 : ℝ))
      (E := (cell12430 ⟨38, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82765095128993 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571557792791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_39 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (20682740048133 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286235128821 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨39, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (20682740048133 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286235128821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12431_20 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (10422952224853 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286024569797 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨20, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (10422952224853 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286024569797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_21 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (8334904965963 / 10000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (285753569597 / 12500000000000 : ℝ))
      (E := (cell12431 ⟨21, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (8334904965963 / 10000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (285753569597 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_22 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (20828626469663 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286032557817 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨22, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (20828626469663 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286032557817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_23 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (5204999151423 / 6250000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286036577179 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨23, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (5204999151423 / 6250000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286036577179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_24 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (20811372814757 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457208112107 / 20000000000000 : ℝ))
      (E := (cell12431 ⟨24, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (20811372814757 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457208112107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_25 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (83211020354651 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457208913993 / 20000000000000 : ℝ))
      (E := (cell12431 ⟨25, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (83211020354651 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457208913993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_26 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (2599267927407 / 3125000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (3657677681 / 160000000000 : ℝ))
      (E := (cell12431 ⟨26, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (2599267927407 / 3125000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (3657677681 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_27 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (83142151193703 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286052564169 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨27, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (83142151193703 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286052564169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_28 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (8310775287241 / 10000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1143028277619 / 50000000000000 : ℝ))
      (E := (cell12431 ⟨28, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (8310775287241 / 10000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1143028277619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_29 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (8307337868103 / 10000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571515146267 / 25000000000000 : ℝ))
      (E := (cell12431 ⟨29, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (8307337868103 / 10000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571515146267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_30 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (83039028587617 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286064539299 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨30, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (83039028587617 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286064539299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_31 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (16600940512077 / 20000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (228606853719 / 10000000000000 : ℝ))
      (E := (cell12431 ⟨31, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (16600940512077 / 20000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (228606853719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_32 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82970400567711 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286072580893 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨32, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82970400567711 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286072580893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_33 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (16587224515627 / 20000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286076555217 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨33, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (16587224515627 / 20000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286076555217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_34 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (20725467140089 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1143040260147 / 50000000000000 : ℝ))
      (E := (cell12431 ⟨34, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (20725467140089 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1143040260147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_35 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (2589613702601 / 3125000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571521134031 / 25000000000000 : ℝ))
      (E := (cell12431 ⟨35, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (2589613702601 / 3125000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571521134031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_36 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (41416716157891 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (57152213633 / 2500000000000 : ℝ))
      (E := (cell12431 ⟨36, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (41416716157891 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (57152213633 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_37 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82799250027179 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286092548827 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨37, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82799250027179 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286092548827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_38 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (20691272896689 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286096547363 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨38, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (20691272896689 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286096547363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_39 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (20682739241 / 25000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (142881283839 / 6250000000000 : ℝ))
      (E := (cell12431 ⟨39, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (20682739241 / 25000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (142881283839 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12432_20 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (20845902134107 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285890057597 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨20, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (20845902134107 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285890057597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_21 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (83349040718859 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285894009241 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨21, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (83349040718859 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285894009241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_22 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (5207156078691 / 6250000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (228589803397 / 10000000000000 : ℝ))
      (E := (cell12432 ⟨22, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (5207156078691 / 6250000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (228589803397 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_23 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (83279978123899 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571475504867 / 25000000000000 : ℝ))
      (E := (cell12432 ⟨23, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (83279978123899 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571475504867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_24 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41622741640219 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285906028029 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨24, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41622741640219 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285906028029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_25 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (83211012695893 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (285738750633 / 12500000000000 : ℝ))
      (E := (cell12432 ⟨25, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (83211012695893 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (285738750633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_26 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (20794141584413 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285914012443 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨26, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (20794141584413 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285914012443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_27 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (10392768021659 / 12500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285917995059 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨27, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (10392768021659 / 12500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285917995059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_28 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41553873085237 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142961007179 / 50000000000000 : ℝ))
      (E := (cell12432 ⟨28, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41553873085237 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142961007179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_29 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (20768343074287 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285926014721 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨29, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (20768343074287 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285926014721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_30 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41519511260673 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (71435312459 / 3125000000000 : ℝ))
      (E := (cell12432 ⟨30, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41519511260673 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (71435312459 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_31 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (83004696811283 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (57148350677 / 2500000000000 : ℝ))
      (E := (cell12432 ⟨31, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (83004696811283 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (57148350677 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_32 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41485197567669 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285937984981 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨32, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41485197567669 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285937984981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_33 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (1658722349241 / 2000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (457188398257 / 20000000000000 : ℝ))
      (E := (cell12432 ⟨33, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (1658722349241 / 2000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (457188398257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_34 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (2072546594003 / 2500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (142871624319 / 6250000000000 : ℝ))
      (E := (cell12432 ⟨34, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (2072546594003 / 2500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (142871624319 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_35 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82867633998407 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142974989917 / 50000000000000 : ℝ))
      (E := (cell12432 ⟨35, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82867633998407 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142974989917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_36 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (8283342814593 / 10000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (228595402327 / 10000000000000 : ℝ))
      (E := (cell12432 ⟨36, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (8283342814593 / 10000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (228595402327 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_37 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (16559849234373 / 20000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571489500781 / 25000000000000 : ℝ))
      (E := (cell12432 ⟨37, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (16559849234373 / 20000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571489500781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_38 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82765088045543 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (14287262367 / 625000000000 : ℝ))
      (E := (cell12432 ⟨38, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82765088045543 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (14287262367 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_39 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82730953736453 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285966009249 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨39, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82730953736453 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285966009249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12433_20 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (16676719855153 / 20000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (71429860661 / 3125000000000 : ℝ))
      (E := (cell12433 ⟨20, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (16676719855153 / 20000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (71429860661 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_21 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83349031779781 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285759574051 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨21, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83349031779781 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285759574051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_22 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83314488641113 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142881782129 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨22, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83314488641113 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142881782129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_23 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83279969826643 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285767515957 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨23, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83279969826643 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285767515957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_24 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (4162273765171 / 5000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285771549787 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨24, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (4162273765171 / 5000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285771549787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_25 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (20802751259667 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285775552861 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨25, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (20802751259667 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285775552861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_26 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83176558999773 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142889764327 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨26, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83176558999773 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142889764327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_27 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41571068577147 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285783538821 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨27, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41571068577147 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285783538821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_28 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41553869734977 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142893763999 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨28, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41553869734977 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142893763999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_29 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41536682957321 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285791557419 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨29, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41536682957321 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285791557419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_30 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83039016456411 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (91431820509 / 4000000000000 : ℝ))
      (E := (cell12433 ⟨30, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83039016456411 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (91431820509 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_31 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41502345531739 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285799513173 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨31, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41502345531739 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285799513173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_32 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82970389704221 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285803502379 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨32, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82970389704221 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285803502379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_33 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82936112347183 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (9143230163 / 400000000000 : ℝ))
      (E := (cell12433 ⟨33, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82936112347183 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (9143230163 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_34 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82901858961063 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142905756409 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨34, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82901858961063 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142905756409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_35 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82867629514723 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285815537113 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨35, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82867629514723 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285815537113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_36 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (4141671198859 / 5000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285819497621 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨36, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (4141671198859 / 5000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285819497621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_37 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82799242317613 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142911756257 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨37, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82799242317613 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142911756257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_38 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41382542252677 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142913761953 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨38, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41382542252677 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142913761953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_39 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82730950509891 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285831532293 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨39, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82730950509891 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285831532293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12434_20 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41691795008417 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (285702642121 / 12500000000000 : ℝ))
      (E := (cell12434 ⟨20, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41691795008417 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (285702642121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_21 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (16669804568479 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (114281256733 / 5000000000000 : ℝ))
      (E := (cell12434 ⟨21, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (16669804568479 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (114281256733 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_22 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41657240012411 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (457125818077 / 20000000000000 : ℝ))
      (E := (cell12434 ⟨22, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41657240012411 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (457125818077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_23 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83279961530999 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (228563312497 / 10000000000000 : ℝ))
      (E := (cell12434 ⟨23, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83279961530999 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (228563312497 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_24 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (10405683415997 / 12500000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571409281453 / 25000000000000 : ℝ))
      (E := (cell12434 ⟨24, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (10405683415997 / 12500000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571409281453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_25 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (1300171834109 / 1562500000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (114282054831 / 5000000000000 : ℝ))
      (E := (cell12434 ⟨25, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (1300171834109 / 1562500000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (114282054831 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_26 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (20794137915847 / 25000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (114282254963 / 5000000000000 : ℝ))
      (E := (cell12434 ⟨26, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (20794137915847 / 25000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (114282254963 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_27 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83142130136771 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (18285192629 / 800000000000 : ℝ))
      (E := (cell12434 ⟨27, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83142130136771 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (18285192629 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_28 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (2597116649089 / 3125000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (14285331851 / 625000000000 : ℝ))
      (E := (cell12434 ⟨28, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (2597116649089 / 3125000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (14285331851 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_29 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83073359533511 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142828548121 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨29, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83073359533511 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142828548121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_30 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (20759752598203 / 25000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285661081413 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨30, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (20759752598203 / 25000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285661081413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_31 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83004685316969 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (228566511249 / 10000000000000 : ℝ))
      (E := (cell12434 ⟨31, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83004685316969 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (228566511249 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_32 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82970384274363 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142834537277 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨32, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82970384274363 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142834537277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_33 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41468053616767 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (4571346173 / 200000000000 : ℝ))
      (E := (cell12434 ⟨33, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41468053616767 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (4571346173 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_34 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (16580370832637 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285677091437 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨34, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (16580370832637 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285677091437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_35 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41433812516089 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142840545379 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨35, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41433812516089 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142840545379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_36 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82833419809531 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285685085633 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨36, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82833419809531 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285685085633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_37 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82799238464423 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285689077 / 100000000000 : ℝ))
      (E := (cell12434 ⟨37, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82799238464423 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285689077 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_38 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82765080966187 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (114284653279 / 5000000000000 : ℝ))
      (E := (cell12434 ⟨38, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82765080966187 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (114284653279 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_39 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82730947284313 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (14285606941 / 625000000000 : ℝ))
      (E := (cell12434 ⟨39, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82730947284313 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (14285606941 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12435_20 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (16676716151927 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285486728543 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨20, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (16676716151927 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285486728543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_21 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (833490139067 / 1000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457098149869 / 20000000000000 : ℝ))
      (E := (cell12435 ⟨21, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (833490139067 / 1000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457098149869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_22 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (10414308926273 / 12500000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (45709894579 / 2000000000000 : ℝ))
      (E := (cell12435 ⟨22, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (10414308926273 / 12500000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (45709894579 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_23 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (83279953236967 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457099745973 / 20000000000000 : ℝ))
      (E := (cell12435 ⟨23, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (83279953236967 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457099745973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_24 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (10405682419263 / 12500000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457100551221 / 20000000000000 : ℝ))
      (E := (cell12435 ⟨24, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (10405682419263 / 12500000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457100551221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_25 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (83210989728817 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285506753079 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨25, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (83210989728817 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285506753079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_26 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (5198534020531 / 6250000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285510724263 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨26, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (5198534020531 / 6250000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285510724263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_27 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (83142123120701 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285514731307 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨27, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (83142123120701 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285514731307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_28 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (83107726073157 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285518718847 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨28, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (83107726073157 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285518718847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_29 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41536676576877 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142761374059 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨29, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41536676576877 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142761374059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_30 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (20759751082637 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142763352377 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨30, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (20759751082637 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142763352377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_31 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (20751169892939 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142765354007 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨31, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (20751169892939 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142765354007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_32 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82970378845761 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (228553470151 / 10000000000000 : ℝ))
      (E := (cell12435 ⟨32, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82970378845761 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (228553470151 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_33 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82936102121103 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142769343547 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨33, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82936102121103 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142769343547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_34 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41450924683243 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285542724963 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨34, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41450924683243 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285542724963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_35 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (20716905137693 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (3656874719 / 160000000000 : ℝ))
      (E := (cell12435 ⟨35, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (20716905137693 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (3656874719 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_36 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41416707821491 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285550728679 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨36, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41416707821491 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285550728679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_37 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41399617306147 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457110939317 / 20000000000000 : ℝ))
      (E := (cell12435 ⟨37, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41399617306147 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457110939317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_38 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41382538714021 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285558721089 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨38, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41382538714021 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285558721089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_39 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41365472029859 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571390671339 / 25000000000000 : ℝ))
      (E := (cell12435 ⟨39, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41365472029859 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571390671339 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12436_20 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41691785752083 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (114267621619 / 5000000000000 : ℝ))
      (E := (cell12436 ⟨20, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41691785752083 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (114267621619 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_21 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83349004972697 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (285669552263 / 12500000000000 : ℝ))
      (E := (cell12436 ⟨21, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83349004972697 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (285669552263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_22 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (20828615699299 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457072084331 / 20000000000000 : ℝ))
      (E := (cell12436 ⟨22, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (20828615699299 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457072084331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_23 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83279944944547 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457072889457 / 20000000000000 : ℝ))
      (E := (cell12436 ⟨23, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83279944944547 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457072889457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_24 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (20811362845451 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457073688133 / 20000000000000 : ℝ))
      (E := (cell12436 ⟨24, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (20811362845451 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457073688133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_25 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (8321098207619 / 10000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142686202751 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨25, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (8321098207619 / 10000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142686202751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_26 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83176536995097 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (114268820183 / 5000000000000 : ℝ))
      (E := (cell12436 ⟨26, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83176536995097 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (114268820183 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_27 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (16628423221217 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285380438447 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨27, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (16628423221217 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285380438447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_28 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83107719376879 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142692198029 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨28, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83107719376879 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142692198029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_29 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (20768336693843 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285388396117 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨29, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (20768336693843 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285388396117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_30 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83038998269619 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457078476549 / 20000000000000 : ℝ))
      (E := (cell12436 ⟨30, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83038998269619 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457078476549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_31 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83004673827839 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142698208381 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨31, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83004673827839 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142698208381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_32 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (16594074683683 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457080076649 / 20000000000000 : ℝ))
      (E := (cell12436 ⟨32, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (16594074683683 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457080076649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_33 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82936097009889 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285404401087 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨33, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82936097009889 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285404401087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_34 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (16580368914193 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (571352103349 / 25000000000000 : ℝ))
      (E := (cell12436 ⟨34, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (16580368914193 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (571352103349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_35 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41433808035253 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (571353105391 / 25000000000000 : ℝ))
      (E := (cell12436 ⟨35, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41433808035253 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (571353105391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_36 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82833411477533 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285416368131 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨36, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82833411477533 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285416368131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_37 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41399615380613 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285420371267 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨37, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41399615380613 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285420371267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_38 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (2069126847273 / 2500000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285424373083 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨38, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (2069126847273 / 2500000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285424373083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_39 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82730940836107 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285428374071 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨39, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82730940836107 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285428374071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12437_20 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (83383562250429 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (228521819023 / 10000000000000 : ℝ))
      (E := (cell12437 ⟨20, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (83383562250429 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (228521819023 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_21 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (16669799208077 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (114261107047 / 5000000000000 : ℝ))
      (E := (cell12437 ⟨21, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (16669799208077 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (114261107047 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_22 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (4165722709293 / 5000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285226168501 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨22, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (4165722709293 / 5000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285226168501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_23 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (83279936653739 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285230160589 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨23, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (83279936653739 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285230160589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_24 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (20811360852769 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457046835899 / 20000000000000 : ℝ))
      (E := (cell12437 ⟨24, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (20811360852769 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457046835899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_25 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (16642194885019 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571309542657 / 25000000000000 : ℝ))
      (E := (cell12437 ⟨25, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (16642194885019 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571309542657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_26 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (8317652966319 / 10000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285242137457 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨26, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (8317652966319 / 10000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285242137457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_27 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (83142109092921 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457049228327 / 20000000000000 : ℝ))
      (E := (cell12437 ⟨27, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (83142109092921 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457049228327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_28 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (16621542536403 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457050025559 / 20000000000000 : ℝ))
      (E := (cell12437 ⟨28, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (16621542536403 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457050025559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_29 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (20768335099591 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285254157169 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨29, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (20768335099591 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285254157169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_30 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (3321559688401 / 4000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (35707158053 / 1562500000000 : ℝ))
      (E := (cell12437 ⟨30, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (3321559688401 / 4000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (35707158053 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_31 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41502334042609 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142631060859 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨31, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41502334042609 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142631060859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_32 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41485183996163 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285266119761 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨32, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41485183996163 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285266119761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_33 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (20734022974973 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285270111369 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨33, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (20734022974973 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285270111369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_34 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41450919888311 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142637078369 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨34, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41450919888311 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142637078369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_35 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41433805795689 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571319535031 / 25000000000000 : ℝ))
      (E := (cell12437 ⟨35, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41433805795689 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571319535031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_36 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (2588543978537 / 3125000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285282121247 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨36, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (2588543978537 / 3125000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285282121247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_37 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (4139961345561 / 5000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285286101047 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨37, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (4139961345561 / 5000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285286101047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_38 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (4138253517741 / 5000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571322534729 / 25000000000000 : ℝ))
      (E := (cell12437 ⟨38, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (4138253517741 / 5000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571322534729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_39 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (82730937613479 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142647059007 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨39, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (82730937613479 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142647059007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12438_20 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41691776499211 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142541971921 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨20, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41691776499211 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142541971921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_21 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83348987109763 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285087976131 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨21, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83348987109763 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285087976131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_22 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (3332577823047 / 4000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285091969489 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨22, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (3332577823047 / 4000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285091969489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_23 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83279928364541 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285095928101 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨23, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83279928364541 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285095928101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_24 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41622717720959 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142549986299 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨24, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41622717720959 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142549986299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_25 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20802741693883 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285103931721 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨25, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20802741693883 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285103931721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_26 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (3327060893311 / 4000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142553962827 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨26, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (3327060893311 / 4000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142553962827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_27 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (8314210208121 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285111957703 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨27, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (8314210208121 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285111957703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_28 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83107705988563 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285115914061 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨28, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83107705988563 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285115914061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_29 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83073334022729 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285119914351 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨29, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83073334022729 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285119914351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_30 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (16607797230353 / 20000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (114256198059 / 5000000000000 : ℝ))
      (E := (cell12438 ⟨30, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (16607797230353 / 20000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (114256198059 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_31 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83004662343891 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457025587981 / 20000000000000 : ℝ))
      (E := (cell12438 ⟨31, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83004662343891 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457025587981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_32 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20742590641873 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142565955531 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨32, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20742590641873 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142565955531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_33 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (10367010848889 / 12500000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142567967527 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨33, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (10367010848889 / 12500000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142567967527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_34 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (2590682343233 / 3125000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285139954991 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨34, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (2590682343233 / 3125000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285139954991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_35 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82867607113389 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285143913657 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨35, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82867607113389 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285143913657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_36 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (16566680629987 / 20000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285147929401 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨36, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (16566680629987 / 20000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285147929401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_37 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82799223062273 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142575972291 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨37, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82799223062273 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142575972291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_38 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41382533409871 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285155901237 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨38, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41382533409871 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285155901237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_39 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41365467195917 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457031983437 / 20000000000000 : ℝ))
      (E := (cell12438 ⟨39, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41365467195917 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457031983437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12439_20 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (5211471484259 / 6250000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284949809723 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨20, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (5211471484259 / 6250000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284949809723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_21 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83348978180831 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142476903563 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨21, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83348978180831 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142476903563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_22 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83314436968139 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284957824623 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨22, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83314436968139 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284957824623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_23 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41639960038477 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142480904071 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨23, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41639960038477 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142480904071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_24 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (20811356868583 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571241454993 / 25000000000000 : ℝ))
      (E := (cell12439 ⟨24, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (20811356868583 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571241454993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_25 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (33284383651 / 40000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284969805519 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨25, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (33284383651 / 40000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284969805519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_26 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (20794128750963 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284973768251 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨26, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (20794128750963 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284973768251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_27 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83142095070951 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284977769819 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨27, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83142095070951 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284977769819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_28 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (20776924824131 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (456996362659 / 20000000000000 : ℝ))
      (E := (cell12439 ⟨28, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (20776924824131 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (456996362659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_29 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (20768331912117 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571246446147 / 25000000000000 : ℝ))
      (E := (cell12439 ⟨29, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (20768331912117 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571246446147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_30 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83038980094839 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284989803139 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨30, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83038980094839 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284989803139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_31 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83004656603859 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284993754301 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨31, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83004656603859 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284993754301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_32 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41485178571957 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (456999551429 / 20000000000000 : ℝ))
      (E := (cell12439 ⟨32, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41485178571957 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (456999551429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_33 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (20734020420887 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (228500175503 / 10000000000000 : ℝ))
      (E := (cell12439 ⟨33, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (20734020420887 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (228500175503 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_34 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82901830191467 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142502874787 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨34, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82901830191467 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142502874787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_35 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41433801318269 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285009800769 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨35, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41433801318269 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285009800769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_36 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (16566679797557 / 20000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (142813362037 / 6250000000000 : ℝ))
      (E := (cell12439 ⟨36, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (16566679797557 / 20000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (142813362037 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_37 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82799219214387 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (457003556913 / 20000000000000 : ℝ))
      (E := (cell12439 ⟨37, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82799219214387 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (457003556913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_38 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (16553012657137 / 20000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285021777399 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨38, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (16553012657137 / 20000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285021777399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_39 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82730931171171 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (35703527681 / 1562500000000 : ℝ))
      (E := (cell12439 ⟨39, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82730931171171 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (35703527681 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12440_20 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83383534499597 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142407864809 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨20, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83383534499597 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142407864809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_21 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83348969253589 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284819692201 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨21, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83348969253589 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284819692201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_22 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83314428361753 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142411866951 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨22, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83314428361753 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142411866951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_23 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83279911790977 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284827684071 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨23, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83279911790977 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284827684071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_24 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (20811354877079 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284831721621 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨24, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (20811354877079 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284831721621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_25 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41605475740499 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142417837643 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨25, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41605475740499 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142417837643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_26 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (4158825383821 / 5000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284839723643 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨26, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (4158825383821 / 5000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284839723643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_27 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83142088062143 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142421847409 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨27, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83142088062143 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142421847409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_28 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41553846302949 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284847708619 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨28, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41553846302949 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284847708619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_29 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83073321275579 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (114242585471 / 5000000000000 : ℝ))
      (E := (cell12440 ⟨29, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83073321275579 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (114242585471 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_30 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41519487019623 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456971139951 / 20000000000000 : ℝ))
      (E := (cell12440 ⟨30, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41519487019623 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456971139951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_31 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83004650865121 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (228485968193 / 10000000000000 : ℝ))
      (E := (cell12440 ⟨31, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83004650865121 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (228485968193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_32 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (8297035172159 / 10000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456972731603 / 20000000000000 : ℝ))
      (E := (cell12440 ⟨32, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (8297035172159 / 10000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456972731603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_33 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (207340191443 / 250000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284867688413 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨33, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (207340191443 / 250000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284867688413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_34 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (5181364087541 / 6250000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (45697433153 / 2000000000000 : ℝ))
      (E := (cell12440 ⟨34, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (5181364087541 / 6250000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (45697433153 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_35 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (3314703926433 / 4000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571218921063 / 25000000000000 : ℝ))
      (E := (cell12440 ⟨35, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (3314703926433 / 4000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571218921063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_36 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82833394826733 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571219913049 / 25000000000000 : ℝ))
      (E := (cell12440 ⟨36, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82833394826733 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571219913049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_37 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82799215367561 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571220919913 / 25000000000000 : ℝ))
      (E := (cell12440 ⟨37, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82799215367561 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571220919913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_38 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82765059752649 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571221912513 / 25000000000000 : ℝ))
      (E := (cell12440 ⟨38, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82765059752649 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571221912513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_39 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82730927951491 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571222920303 / 25000000000000 : ℝ))
      (E := (cell12440 ⟨39, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82730927951491 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571222920303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12441_20 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41691762626389 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284681703533 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨20, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41691762626389 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284681703533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_21 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (20837240082009 / 25000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456937137927 / 20000000000000 : ℝ))
      (E := (cell12441 ⟨21, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (20837240082009 / 25000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456937137927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_22 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83314419757017 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284689697327 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨22, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83314419757017 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284689697327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_23 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83279903506609 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456938734507 / 20000000000000 : ℝ))
      (E := (cell12441 ⟨23, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83279903506609 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456938734507 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_24 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (8324541154387 / 10000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456939535509 / 20000000000000 : ℝ))
      (E := (cell12441 ⟨24, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (8324541154387 / 10000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456939535509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_25 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83210943836027 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142350828881 / 50000000000000 : ℝ))
      (E := (cell12441 ⟨25, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83210943836027 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142350828881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_26 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83176500350479 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142352837523 / 50000000000000 : ℝ))
      (E := (cell12441 ⟨26, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83176500350479 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142352837523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_27 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83142081054787 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571177418571 / 25000000000000 : ℝ))
      (E := (cell12441 ⟨27, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83142081054787 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571177418571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_28 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83107685916683 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (91388546339 / 4000000000000 : ℝ))
      (E := (cell12441 ⟨28, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83107685916683 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (91388546339 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_29 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83073314904063 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284717630383 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨29, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83073314904063 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284717630383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_30 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83038967984987 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284721651031 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨30, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83038967984987 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284721651031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_31 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41502322563839 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (57118141607 / 2500000000000 : ℝ))
      (E := (cell12441 ⟨31, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41502322563839 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (57118141607 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_32 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41485173150261 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571182418051 / 25000000000000 : ℝ))
      (E := (cell12441 ⟨32, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41485173150261 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571182418051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_33 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82936071472067 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284733618089 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨33, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82936071472067 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284733618089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_34 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82901820611021 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (14279610129 / 625000000000 : ℝ))
      (E := (cell12441 ⟨34, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82901820611021 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (14279610129 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_35 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (66294074949 / 80000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284741622713 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨35, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (66294074949 / 80000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284741622713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_36 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (4141669533339 / 5000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284745625469 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨36, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (4141669533339 / 5000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284745625469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_37 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (16559842304359 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284749629843 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨37, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (16559842304359 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284749629843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_38 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41382528110317 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571188409137 / 25000000000000 : ℝ))
      (E := (cell12441 ⟨38, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41382528110317 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571188409137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_39 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (10341365591599 / 12500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285594705759 / 12500000000000 : ℝ))
      (E := (cell12441 ⟨39, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (10341365591599 / 12500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285594705759 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12442_20 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83383516007687 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (17848028697 / 781250000000 : ℝ))
      (E := (cell12442 ⟨20, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83383516007687 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (17848028697 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_21 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83348951404171 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142275841439 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨21, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83348951404171 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142275841439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_22 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (8331441115393 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142277828301 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨22, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (8331441115393 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142277828301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_23 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (1665597904477 / 2000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285569957111 / 12500000000000 : ℝ))
      (E := (cell12442 ⟨23, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (1665597904477 / 2000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285569957111 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_24 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83245403580993 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142281843873 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨24, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83245403580993 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142281843873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_25 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (41605468096293 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284567694579 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨25, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (41605468096293 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284567694579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_26 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (20794123256507 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284571680853 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨26, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (20794123256507 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284571680853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_27 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (41571037024441 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142287824901 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨27, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (41571037024441 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142287824901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_28 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (1038845990361 / 1250000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284579662863 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨28, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (1038845990361 / 1250000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284579662863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_29 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83073308533919 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284583664407 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨29, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83073308533919 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284583664407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_30 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (4151948096603 / 5000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284587656967 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨30, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (4151948096603 / 5000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284587656967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_31 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83004639391527 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142295821423 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨31, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83004639391527 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142295821423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_32 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (20742585220177 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285574460331 / 12500000000000 : ℝ))
      (E := (cell12442 ⟨32, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (20742585220177 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285574460331 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_33 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (1658721327363 / 2000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284599661173 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨33, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (1658721327363 / 2000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284599661173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_34 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82901815822561 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284603638547 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨34, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82901815822561 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284603638547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_35 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82867589212811 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142303837379 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨35, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82867589212811 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142303837379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_36 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (3313335460317 / 4000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285576456723 / 12500000000000 : ℝ))
      (E := (cell12442 ⟨36, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (3313335460317 / 4000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285576456723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_37 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (2587475239909 / 3125000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (114230781757 / 5000000000000 : ℝ))
      (E := (cell12442 ⟨37, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (2587475239909 / 3125000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (114230781757 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_38 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82765052689639 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142309839107 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨38, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82765052689639 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142309839107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_39 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (20682730378769 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284623666163 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨39, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (20682730378769 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284623666163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12443_20 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (3335340270573 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284413755171 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨20, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (3335340270573 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284413755171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_21 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (16669788496399 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142208894241 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨21, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (16669788496399 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142208894241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_22 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83314402552491 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (91376869133 / 4000000000000 : ℝ))
      (E := (cell12443 ⟨22, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83314402552491 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (91376869133 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_23 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83279886942701 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284425753777 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨23, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83279886942701 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284425753777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_24 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41622697809843 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (71388429757 / 3125000000000 : ℝ))
      (E := (cell12443 ⟨24, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41622697809843 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (71388429757 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_25 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (3328437142027 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285554215921 / 12500000000000 : ℝ))
      (E := (cell12443 ⟨25, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (3328437142027 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285554215921 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_26 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83176485703067 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284437741067 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨26, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83176485703067 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284437741067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_27 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83142067044427 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (71388804319 / 3125000000000 : ℝ))
      (E := (cell12443 ⟨27, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83142067044427 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (71388804319 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_28 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (10388459067811 / 12500000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456889144357 / 20000000000000 : ℝ))
      (E := (cell12443 ⟨28, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (10388459067811 / 12500000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456889144357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_29 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83073302165147 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (571112438257 / 25000000000000 : ℝ))
      (E := (cell12443 ⟨29, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83073302165147 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (571112438257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_30 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41519477940233 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456890743513 / 20000000000000 : ℝ))
      (E := (cell12443 ⟨30, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41519477940233 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456890743513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_31 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (8300463365667 / 10000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284457734647 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨31, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (8300463365667 / 10000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284457734647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_32 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (20742583865537 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142230873941 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨32, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (20742583865537 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142230873941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_33 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (82936061265447 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285558219889 / 12500000000000 : ℝ))
      (E := (cell12443 ⟨33, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (82936061265447 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285558219889 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_34 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41450905517639 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285558713921 / 12500000000000 : ℝ))
      (E := (cell12443 ⟨34, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41450905517639 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285558713921 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_35 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (8286758474051 / 10000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284473723177 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨35, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (8286758474051 / 10000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284473723177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_36 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (82833382350169 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284477737141 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨36, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (82833382350169 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284477737141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_37 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (517495023959 / 625000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456896350839 / 20000000000000 : ℝ))
      (E := (cell12443 ⟨37, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (517495023959 / 625000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456896350839 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_38 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (16553009831933 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284485716373 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨38, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (16553009831933 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284485716373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_39 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (82730918298341 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284489741489 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨39, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (82730918298341 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284489741489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12444_20 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (8338349752269 / 10000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571069972787 / 25000000000000 : ℝ))
      (E := (cell12444 ⟨20, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (8338349752269 / 10000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571069972787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_21 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83348933561507 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (456856777979 / 20000000000000 : ℝ))
      (E := (cell12444 ⟨21, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83348933561507 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (456856777979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_22 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (833143939527 / 1000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284287854199 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨22, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (833143939527 / 1000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284287854199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_23 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83279878663159 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284291904881 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨23, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83279878663159 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284291904881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_24 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83245387659947 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284295870981 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨24, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83245387659947 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284295870981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_25 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (20802730227573 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (228429987287 / 10000000000000 : ℝ))
      (E := (cell12444 ⟨25, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (20802730227573 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (228429987287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_26 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (16635295676319 / 20000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285537981961 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨26, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (16635295676319 / 20000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285537981961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_27 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41571030020711 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571076970271 / 25000000000000 : ℝ))
      (E := (cell12444 ⟨27, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41571030020711 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571076970271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_28 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83107665857507 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142155946841 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨28, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83107665857507 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142155946841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_29 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41536647898873 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285539479723 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨29, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41536647898873 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285539479723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_30 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (20759737457551 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (142769993207 / 6250000000000 : ℝ))
      (E := (cell12444 ⟨30, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (20759737457551 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (142769993207 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_31 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41502313961553 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142161940587 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨31, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41502313961553 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142161940587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_32 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82970330044841 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (4461577867 / 195312500000 : ℝ))
      (E := (cell12444 ⟨32, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82970330044841 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (4461577867 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_33 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (2073401404099 / 2500000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284331853343 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨33, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (2073401404099 / 2500000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284331853343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_34 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82901806249171 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142167919553 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨34, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82901806249171 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142167919553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_35 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (2589611883417 / 3125000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142169913289 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨35, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (2589611883417 / 3125000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142169913289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_36 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82833378193509 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284343875543 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨36, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82833378193509 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284343875543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_37 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (1655983999817 / 2000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142173934853 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨37, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (1655983999817 / 2000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142173934853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_38 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (8276504563071 / 10000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284351868379 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨38, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (8276504563071 / 10000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284351868379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_39 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41365457541293 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (142772242003 / 6250000000000 : ℝ))
      (E := (cell12444 ⟨39, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41365457541293 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (142772242003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12445_20 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41691744141391 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284146081149 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨20, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41691744141391 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284146081149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_21 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41674462321353 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284150045397 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨21, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41674462321353 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284150045397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_22 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (20828596338639 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (91366163701 / 4000000000000 : ℝ))
      (E := (cell12445 ⟨22, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (20828596338639 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (91366163701 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_23 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41639935192613 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284158051879 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨23, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41639935192613 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284158051879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_24 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (5202836231361 / 6250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (114208102201 / 5000000000000 : ℝ))
      (E := (cell12445 ⟨24, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (5202836231361 / 6250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (114208102201 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_25 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83210913271439 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571041518179 / 25000000000000 : ℝ))
      (E := (cell12445 ⟨25, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83210913271439 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571041518179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_26 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83176471061613 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142085012359 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨26, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83176471061613 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142085012359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_27 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (20785513259967 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (71380439951 / 3125000000000 : ℝ))
      (E := (cell12445 ⟨27, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (20785513259967 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (71380439951 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_28 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (5194228698371 / 6250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571044515419 / 25000000000000 : ℝ))
      (E := (cell12445 ⟨28, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (5194228698371 / 6250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571044515419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_29 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (20768322357929 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456836407121 / 20000000000000 : ℝ))
      (E := (cell12445 ⟨29, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (20768322357929 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456836407121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_30 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41519471890637 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571046515309 / 25000000000000 : ℝ))
      (E := (cell12445 ⟨30, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41519471890637 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571046515309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_31 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (16600924438167 / 20000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142095011959 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨31, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (16600924438167 / 20000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142095011959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_32 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (20742581157197 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284194042719 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨32, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (20742581157197 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284194042719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_33 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41468025531843 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284198060991 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨33, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41468025531843 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284198060991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_34 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41450900732119 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456840404353 / 20000000000000 : ℝ))
      (E := (cell12445 ⟨34, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41450900732119 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456840404353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_35 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (20716893949829 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571051510891 / 25000000000000 : ℝ))
      (E := (cell12445 ⟨35, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (20716893949829 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571051510891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_36 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82833374037947 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284210010363 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨36, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82833374037947 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284210010363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_37 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82799196149319 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284214040327 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨37, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82799196149319 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284214040327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_38 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (3310601684111 / 4000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284218016883 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨38, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (3310601684111 / 4000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284218016883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_39 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82730911867813 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284222057843 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨39, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82730911867813 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284222057843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12446_20 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41691739522301 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142006162587 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨20, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41691739522301 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142006162587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_21 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (10418614465699 / 12500000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284016313263 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨21, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (10418614465699 / 12500000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284016313263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_22 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (4165718837903 / 5000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (142751270419 / 6250000000000 : ℝ))
      (E := (cell12446 ⟨22, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (4165718837903 / 5000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (142751270419 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_23 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (832798621089 / 1000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284024311417 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨23, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (832798621089 / 1000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284024311417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_24 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83245371745173 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284028271339 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨24, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83245371745173 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284028271339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_25 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83210905634113 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284032268539 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨25, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83210905634113 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284032268539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_26 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (1039705796789 / 1250000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (45680726131 / 2000000000000 : ℝ))
      (E := (cell12446 ⟨26, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (1039705796789 / 1250000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (45680726131 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_27 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41571023019881 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142020135919 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨27, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41571023019881 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142020135919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_28 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41553826245887 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (142752767763 / 6250000000000 : ℝ))
      (E := (cell12446 ⟨28, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41553826245887 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (142752767763 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_29 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83073283067057 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284048288027 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨29, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83073283067057 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284048288027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_30 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (3321557509347 / 4000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142026142913 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨30, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (3321557509347 / 4000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142026142913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_31 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (16600923291971 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284056279903 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨31, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (16600923291971 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284056279903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_32 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (20742579803497 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284060272327 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨32, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (20742579803497 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284060272327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_33 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41468022982313 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (285508033117 / 12500000000000 : ℝ))
      (E := (cell12446 ⟨33, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41468022982313 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (285508033117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_34 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (518136229253 / 625000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284068259343 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨34, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (518136229253 / 625000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284068259343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_35 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82867571330423 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (228407225693 / 10000000000000 : ℝ))
      (E := (cell12446 ⟨35, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82867571330423 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (228407225693 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_36 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41416684941741 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142038129429 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨36, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41416684941741 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142038129429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_37 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82799192308847 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (285510033257 / 12500000000000 : ℝ))
      (E := (cell12446 ⟨37, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82799192308847 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (285510033257 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_38 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82765038575859 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456816855847 / 20000000000000 : ℝ))
      (E := (cell12446 ⟨38, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82765038575859 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456816855847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_39 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (4136545432701 / 5000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284088240177 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨39, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (4136545432701 / 5000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284088240177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12447_20 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83383469808147 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283878623227 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨20, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83383469808147 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283878623227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_21 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (20837226702541 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141941288473 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨21, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (20837226702541 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141941288473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_22 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83314368163211 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283886615039 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨22, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83314368163211 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283886615039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_23 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83279853834181 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (570972641713 / 25000000000000 : ℝ))
      (E := (cell12447 ⟨23, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83279853834181 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (570972641713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_24 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (41622681895069 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (228389461129 / 10000000000000 : ℝ))
      (E := (cell12447 ⟨24, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (41622681895069 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (228389461129 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_25 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (20802724499579 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283898577079 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨25, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (20802724499579 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283898577079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_26 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16635291285223 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283902584401 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨26, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16635291285223 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283902584401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_27 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16628407808221 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141953289069 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨27, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16628407808221 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141953289069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_28 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83107645811023 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283910561279 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨28, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83107645811023 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283910561279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_29 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (10384159587971 / 12500000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141957297527 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨29, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (10384159587971 / 12500000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141957297527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_30 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83038931687407 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283918565083 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨30, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83038931687407 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283918565083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_31 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83004610730167 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283922590619 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨31, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83004610730167 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283922590619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_32 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82970313800441 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (285490819591 / 12500000000000 : ℝ))
      (E := (cell12447 ⟨32, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82970313800441 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (285490819591 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_33 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (4146802043339 / 5000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283930582297 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨33, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (4146802043339 / 5000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283930582297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_34 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82901791897897 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283934551843 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨34, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82901791897897 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283934551843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_35 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16573513372533 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283938583887 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨35, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16573513372533 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283938583887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_36 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (41416682865057 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141971281201 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨36, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (41416682865057 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141971281201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_37 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82799188469431 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (22839465469 / 1000000000000 : ℝ))
      (E := (cell12447 ⟨37, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82799188469431 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (22839465469 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_38 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82765035049963 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141975269043 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨38, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82765035049963 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141975269043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_39 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (10341363180151 / 12500000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283954536447 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨39, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (10341363180151 / 12500000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283954536447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12448_20 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41691730286709 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141872458527 / 50000000000000 : ℝ))
      (E := (cell12448 ⟨20, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41691730286709 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141872458527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_21 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41674448948211 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (456749790599 / 20000000000000 : ℝ))
      (E := (cell12448 ⟨21, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41674448948211 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (456749790599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_22 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (10414294946251 / 12500000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283752957529 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨22, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (10414294946251 / 12500000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283752957529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_23 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83279845561069 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283756934829 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨23, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83279845561069 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283756934829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_24 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (8324535583667 / 10000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (285470118397 / 12500000000000 : ℝ))
      (E := (cell12448 ⟨24, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (8324535583667 / 10000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (285470118397 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_25 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (16642178072809 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283764939967 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨25, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (16642178072809 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283764939967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_26 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41588224555299 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (285471114583 / 12500000000000 : ℝ))
      (E := (cell12448 ⟨26, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41588224555299 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (285471114583 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_27 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83142032043897 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283772938911 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨27, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83142032043897 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283772938911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_28 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83107639131681 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283776892889 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨28, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83107639131681 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283776892889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_29 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83073270341849 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141890449109 / 50000000000000 : ℝ))
      (E := (cell12448 ⟨29, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83073270341849 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141890449109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_30 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (8303892564247 / 10000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141892449503 / 50000000000000 : ℝ))
      (E := (cell12448 ⟨30, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (8303892564247 / 10000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141892449503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_31 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83004605001771 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141894448777 / 50000000000000 : ℝ))
      (E := (cell12448 ⟨31, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83004605001771 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141894448777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_32 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41485154194073 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570948223981 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨32, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41485154194073 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570948223981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_33 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82936035770147 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141898447979 / 50000000000000 : ℝ))
      (E := (cell12448 ⟨33, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82936035770147 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141898447979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_34 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (10362723389561 / 12500000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (35684389051 / 1562500000000 : ℝ))
      (E := (cell12448 ⟨34, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (10362723389561 / 12500000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (35684389051 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_35 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82867562396043 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283804907223 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨35, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82867562396043 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283804907223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_36 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41416680788921 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283808920993 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨36, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41416680788921 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283808920993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_37 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41399592315537 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283812882853 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨37, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41399592315537 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283812882853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_38 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (16553006305017 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570954227697 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨38, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (16553006305017 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570954227697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_39 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (132369443567 / 160000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570955221989 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨39, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (132369443567 / 160000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570955221989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12449_20 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (16676690268083 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141805661581 / 50000000000000 : ℝ))
      (E := (cell12449 ⟨20, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (16676690268083 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141805661581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_21 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41674444492183 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283615324861 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨21, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41674444492183 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283615324861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_22 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83314350978451 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283619354177 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨22, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83314350978451 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283619354177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_23 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83279837289563 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283623357029 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨23, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83279837289563 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283623357029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_24 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (2601417121399 / 3125000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283627337349 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨24, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (2601417121399 / 3125000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283627337349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_25 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41605441365651 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456726259767 / 20000000000000 : ℝ))
      (E := (cell12449 ⟨25, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41605441365651 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456726259767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_26 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83176441796569 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (114181765167 / 5000000000000 : ℝ))
      (E := (cell12449 ⟨26, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83176441796569 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (114181765167 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_27 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41571012524069 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456727859149 / 20000000000000 : ℝ))
      (E := (cell12449 ⟨27, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41571012524069 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456727859149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_28 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83107632453747 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283643337483 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨28, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83107632453747 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283643337483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_29 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (830732639813 / 1000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283647314453 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨29, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (830732639813 / 1000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283647314453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_30 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41519459799431 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283651346089 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨30, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41519459799431 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283651346089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_31 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41502299637333 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283655317733 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨31, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41502299637333 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283655317733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_32 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82970302977103 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283659289917 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨32, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82970302977103 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283659289917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_33 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82936030674727 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283663323037 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨33, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82936030674727 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283663323037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_34 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82901782336253 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283667301609 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨34, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82901782336253 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283667301609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_35 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (16573511586111 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283671285547 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨35, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (16573511586111 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283671285547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_36 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (16566671485333 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283675334637 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨36, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (16566671485333 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283675334637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_37 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82799180793773 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141839666287 / 50000000000000 : ℝ))
      (E := (cell12449 ⟨37, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82799180793773 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141839666287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_38 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (3310601120049 / 4000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283683279993 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨38, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (3310601120049 / 4000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283683279993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_39 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41365449509261 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456737458941 / 20000000000000 : ℝ))
      (E := (cell12449 ⟨39, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41365449509261 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456737458941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

end BstLean.Part268
