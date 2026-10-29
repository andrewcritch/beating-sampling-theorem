import BstLean.Part268CellShard3Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12425_0 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (8408024317171 / 10000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (114337656457 / 5000000000000 : ℝ))
      (E := (cell12425 ⟨0, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (8408024317171 / 10000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (114337656457 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_1 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (1050564733177 / 1250000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286757139111 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨1, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (1050564733177 / 1250000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286757139111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_2 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (10501267399707 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286761136531 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨2, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (10501267399707 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286761136531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_3 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (16795024953083 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285845641349 / 12500000000000 : ℝ))
      (E := (cell12425 ⟨3, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (16795024953083 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285845641349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_4 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83940135320849 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571692282757 / 25000000000000 : ℝ))
      (E := (cell12425 ⟨4, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83940135320849 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571692282757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_5 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83905170827563 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571693272053 / 25000000000000 : ℝ))
      (E := (cell12425 ⟨5, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83905170827563 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571693272053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_6 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41935115624677 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228677706881 / 10000000000000 : ℝ))
      (E := (cell12425 ⟨6, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41935115624677 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228677706881 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_7 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83835316550209 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286781081181 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨7, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83835316550209 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286781081181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_8 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (16760085338861 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286785075457 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨8, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (16760085338861 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286785075457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_9 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83765561646007 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285848632427 / 12500000000000 : ℝ))
      (E := (cell12425 ⟨9, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83765561646007 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285848632427 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_10 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83730721369867 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286793098597 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨10, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83730721369867 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286793098597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_11 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (4184795291531 / 5000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (457359416853 / 20000000000000 : ℝ))
      (E := (cell12425 ⟨11, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (4184795291531 / 5000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (457359416853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_12 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (8366111499319 / 10000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285850135179 / 12500000000000 : ℝ))
      (E := (cell12425 ⟨12, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (8366111499319 / 10000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (285850135179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_13 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (2090658720567 / 2500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (35731328731 / 1562500000000 : ℝ))
      (E := (cell12425 ⟨13, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (2090658720567 / 2500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (35731328731 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_14 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41795803642189 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286809078991 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨14, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41795803642189 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286809078991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_15 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (2673820491 / 3200000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286813034001 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨15, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (2673820491 / 3200000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286813034001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_16 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (20880549491611 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286817026013 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨16, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (20880549491611 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286817026013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_17 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (16697506023657 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228682106081 / 10000000000000 : ℝ))
      (E := (cell12425 ⟨17, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (16697506023657 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228682106081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_18 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83452886765277 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (91473001101 / 4000000000000 : ℝ))
      (E := (cell12425 ⟨18, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83452886765277 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (91473001101 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_19 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (83418267873599 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571707261941 / 25000000000000 : ℝ))
      (E := (cell12425 ⟨19, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (83418267873599 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571707261941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12426_0 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (21020056841423 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (457323647309 / 20000000000000 : ℝ))
      (E := (cell12426 ⟨0, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (21020056841423 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (457323647309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_1 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (16809032635841 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143311126763 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨1, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (16809032635841 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143311126763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_2 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (42005062026647 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286626200919 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨2, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (42005062026647 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286626200919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_3 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83975109951177 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1829304163 / 80000000000 : ℝ))
      (E := (cell12426 ⟨3, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83975109951177 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1829304163 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_4 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (20985030209067 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286634213343 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨4, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (20985030209067 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286634213343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_5 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41952578336087 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (228663823857 / 10000000000000 : ℝ))
      (E := (cell12426 ⟨5, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41952578336087 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (228663823857 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_6 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (8387021742269 / 10000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (18293137841 / 800000000000 : ℝ))
      (E := (cell12426 ⟨6, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (8387021742269 / 10000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (18293137841 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_7 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83835303051807 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286646196291 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨7, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83835303051807 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286646196291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_8 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41900206761851 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (228665020307 / 10000000000000 : ℝ))
      (E := (cell12426 ⟨8, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41900206761851 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (228665020307 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_9 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (4188277440137 / 5000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (571663550079 / 25000000000000 : ℝ))
      (E := (cell12426 ⟨9, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (4188277440137 / 5000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (571663550079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_10 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41865354426737 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (71458068611 / 3125000000000 : ℝ))
      (E := (cell12426 ⟨10, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41865354426737 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (71458068611 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_11 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83695893640643 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286662196047 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨11, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83695893640643 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286662196047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_12 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (5228818945573 / 6250000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (91466648353 / 4000000000000 : ℝ))
      (E := (cell12426 ⟨12, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (5228818945573 / 6250000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (91466648353 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_13 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (16725267456831 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286670182567 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨13, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (16725267456831 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286670182567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_14 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (20897899017723 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (457334836367 / 20000000000000 : ℝ))
      (E := (cell12426 ⟨14, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (20897899017723 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (457334836367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_15 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83556879454847 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286678154769 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨15, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83556879454847 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286678154769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_16 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83522187401669 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143341082741 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨16, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83522187401669 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143341082741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_17 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (83487519877183 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286686161579 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨17, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (83487519877183 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286686161579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_18 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (16690575369479 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286690148523 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨18, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (16690575369479 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286690148523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_19 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (20854564569621 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286694131541 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨19, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (20854564569621 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286694131541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12427_0 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (4204010578111 / 5000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285810424581 / 12500000000000 : ℝ))
      (E := (cell12427 ⟨0, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (4204010578111 / 5000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285810424581 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_1 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (16809029541351 / 20000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457297484141 / 20000000000000 : ℝ))
      (E := (cell12427 ⟨1, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (16809029541351 / 20000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457297484141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_2 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (21002527227849 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457298275193 / 20000000000000 : ℝ))
      (E := (cell12427 ⟨2, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (21002527227849 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457298275193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_3 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83975095139363 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286495387453 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨3, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83975095139363 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286495387453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_4 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83940106354071 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571624851623 / 25000000000000 : ℝ))
      (E := (cell12427 ⟨4, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83940106354071 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571624851623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_5 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41952571259563 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457300676811 / 20000000000000 : ℝ))
      (E := (cell12427 ⟨5, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41952571259563 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457300676811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_6 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (10483775449791 / 12500000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286507386607 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨6, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (10483775449791 / 12500000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286507386607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_7 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41917644777833 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571627841139 / 25000000000000 : ℝ))
      (E := (cell12427 ⟨7, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41917644777833 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571627841139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_8 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41900200177659 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (71453605747 / 3125000000000 : ℝ))
      (E := (cell12427 ⟨8, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41900200177659 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (71453605747 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_9 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (20941383990413 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143259697251 / 50000000000000 : ℝ))
      (E := (cell12427 ⟨9, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (20941383990413 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143259697251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_10 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (4186534816961 / 5000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286523345857 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨10, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (4186534816961 / 5000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286523345857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_11 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83695881452763 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286527361247 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨11, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83695881452763 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286527361247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_12 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41830545633601 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286531331637 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨12, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41830545633601 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286531331637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_13 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41813162873823 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286535321811 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨13, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41813162873823 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286535321811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_14 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41795792429691 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (228653933829 / 10000000000000 : ℝ))
      (E := (cell12427 ⟨14, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41795792429691 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (228653933829 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_15 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (2088921714197 / 2500000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286543329213 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨15, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (2088921714197 / 2500000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286543329213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_16 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83522176838789 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143273679347 / 50000000000000 : ℝ))
      (E := (cell12427 ⟨16, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83522176838789 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143273679347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_17 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (83487509637937 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285818914519 / 12500000000000 : ℝ))
      (E := (cell12427 ⟨17, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (83487509637937 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285818914519 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_18 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (651975522901 / 781250000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2232964183 / 97656250000 : ℝ))
      (E := (cell12427 ⟨18, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (651975522901 / 781250000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2232964183 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_19 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (10427281085643 / 12500000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (57163983187 / 2500000000000 : ℝ))
      (E := (cell12427 ⟨19, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (10427281085643 / 12500000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (57163983187 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12428_0 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (5255012235081 / 6250000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (228634866723 / 10000000000000 : ℝ))
      (E := (cell12428 ⟨0, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (5255012235081 / 6250000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (228634866723 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_1 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (8404513223681 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (285794080081 / 12500000000000 : ℝ))
      (E := (cell12428 ⟨1, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (8404513223681 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (285794080081 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_2 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (42005046885981 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286356603841 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨2, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (42005046885981 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286356603841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_3 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (20993770082493 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571590156013 / 25000000000000 : ℝ))
      (E := (cell12428 ⟨3, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (20993770082493 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571590156013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_4 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (5246255742141 / 6250000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143182297363 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨4, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (5246255742141 / 6250000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143182297363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_5 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (4195256418421 / 5000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457273728093 / 20000000000000 : ℝ))
      (E := (cell12428 ⟨5, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (4195256418421 / 5000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457273728093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_6 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41935094888133 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (114318629809 / 5000000000000 : ℝ))
      (E := (cell12428 ⟨6, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41935094888133 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (114318629809 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_7 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (10479409507723 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286376585979 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨7, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (10479409507723 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286376585979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_8 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (83800387189153 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (57159515449 / 2500000000000 : ℝ))
      (E := (cell12428 ⟨8, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (83800387189153 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (57159515449 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_9 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41882761561371 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286384583983 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨9, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41882761561371 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286384583983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_10 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (2616583869597 / 3125000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286388607531 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨10, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (2616583869597 / 3125000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286388607531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_11 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (4184793463349 / 5000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (285799072483 / 12500000000000 : ℝ))
      (E := (cell12428 ⟨11, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (4184793463349 / 5000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (285799072483 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_12 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41830539703647 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143198282997 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨12, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41830539703647 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143198282997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_13 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (83626314213153 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286400572689 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨13, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (83626314213153 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286400572689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_14 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (10448946706231 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286404548357 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨14, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (10448946706231 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286404548357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_15 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (83556857682849 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143204278667 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨15, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (83556857682849 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143204278667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_16 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (16704433255561 / 20000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (228641254749 / 10000000000000 : ℝ))
      (E := (cell12428 ⟨16, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (16704433255561 / 20000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (228641254749 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_17 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (16697499880109 / 20000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143208291357 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨17, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (16697499880109 / 20000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143208291357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_18 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (20863214254269 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286420552133 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨18, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (20863214254269 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286420552133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_19 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41709119546789 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571606144339 / 25000000000000 : ℝ))
      (E := (cell12428 ⟨19, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41709119546789 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571606144339 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12429_0 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (84080179962917 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286213932729 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨0, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (84080179962917 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286213932729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_1 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (84045116769371 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143108956677 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨1, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (84045116769371 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143108956677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_2 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (5250629914687 / 6250000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (285777742797 / 12500000000000 : ℝ))
      (E := (cell12429 ⟨2, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (5250629914687 / 6250000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (285777742797 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_3 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20993766380751 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143112956773 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨3, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20993766380751 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143112956773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_4 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (41970038698411 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143114946899 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨4, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (41970038698411 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143114946899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_5 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (16781022844011 / 20000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143116946001 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨5, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (16781022844011 / 20000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143116946001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_6 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (10483771994563 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286237916769 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨6, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (10483771994563 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286237916769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_7 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83835262570161 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457248383701 / 20000000000000 : ℝ))
      (E := (cell12429 ⟨7, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83835262570161 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457248383701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_8 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83800374025207 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286245905239 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨8, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83800374025207 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286245905239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_9 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83765510286009 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457249976949 / 20000000000000 : ℝ))
      (E := (cell12429 ⟨9, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83765510286009 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457249976949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_10 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20932667829281 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286253864543 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨10, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20932667829281 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286253864543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_11 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83695857083293 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (22862578519 / 1000000000000 : ℝ))
      (E := (cell12429 ⟨11, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83695857083293 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (22862578519 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_12 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83661067549441 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457252370767 / 20000000000000 : ℝ))
      (E := (cell12429 ⟨12, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83661067549441 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457252370767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_13 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20906575670169 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143132938557 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨13, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20906575670169 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143132938557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_14 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (8359156244229 / 10000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143134935073 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨14, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (8359156244229 / 10000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143134935073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_15 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (10444605849969 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143136919567 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨15, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (10444605849969 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143136919567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_16 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20880538929679 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457255569637 / 20000000000000 : ℝ))
      (E := (cell12429 ⟨16, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20880538929679 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457255569637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_17 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83487489165009 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286281844901 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨17, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83487489165009 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286281844901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_18 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (41726423552319 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143142917373 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨18, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (41726423552319 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143142917373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_19 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (83418229503787 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286289822941 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨19, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (83418229503787 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286289822941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12430_0 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (21020041041771 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286079250929 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨0, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (21020041041771 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286079250929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_1 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (16809020260887 / 20000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286083238829 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨1, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (16809020260887 / 20000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286083238829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_2 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (42005031750243 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143043637957 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨2, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (42005031750243 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143043637957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_3 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41987525359229 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143045627969 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨3, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41987525359229 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143045627969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_4 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (83940062921769 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143047622917 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨4, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (83940062921769 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143047622917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_5 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (8390510007403 / 10000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571524813617 / 25000000000000 : ℝ))
      (E := (cell12430 ⟨5, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (8390510007403 / 10000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571524813617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_6 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41935081069521 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286103232529 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨6, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41935081069521 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286103232529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_7 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (83835249080797 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (457221449249 / 20000000000000 : ℝ))
      (E := (cell12430 ⟨7, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (83835249080797 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (457221449249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_8 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41900180431739 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (142881952859 / 6250000000000 : ℝ))
      (E := (cell12430 ⟨8, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41900180431739 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (142881952859 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_9 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41882748725727 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286115238797 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨9, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41882748725727 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286115238797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_10 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41865329404641 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (91444769317 / 4000000000000 : ℝ))
      (E := (cell12430 ⟨10, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41865329404641 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (91444769317 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_11 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (83695844901703 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571530808849 / 25000000000000 : ℝ))
      (E := (cell12430 ⟨11, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (83695844901703 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571530808849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_12 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (20915263923411 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286127195161 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨12, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (20915263923411 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286127195161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_13 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41813145575107 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571532808773 / 25000000000000 : ℝ))
      (E := (cell12430 ⟨13, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41813145575107 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571532808773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_14 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41795775618353 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286135187443 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨14, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41795775618353 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286135187443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_15 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (8355683591859 / 10000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143069587307 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨15, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (8355683591859 / 10000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143069587307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_16 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (1044026814519 / 1250000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286143202627 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨16, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (1044026814519 / 1250000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286143202627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_17 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41743739465663 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (57153680477 / 2500000000000 : ℝ))
      (E := (cell12430 ⟨17, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41743739465663 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (57153680477 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_18 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41726418597007 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143075585617 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨18, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41726418597007 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143075585617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_19 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (8341821991577 / 10000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286155180693 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨19, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (8341821991577 / 10000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286155180693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12431_0 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (16816029674759 / 20000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457188935923 / 20000000000000 : ℝ))
      (E := (cell12431 ⟨0, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (16816029674759 / 20000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457188935923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_1 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (84045085842003 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285948674877 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨1, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (84045085842003 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285948674877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_2 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (84010048368441 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285952662287 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨2, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (84010048368441 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285952662287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_3 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (83975035916333 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (228595665123 / 10000000000000 : ℝ))
      (E := (cell12431 ⟨3, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (83975035916333 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (228595665123 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_4 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (83940048449097 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1142980325417 / 50000000000000 : ℝ))
      (E := (cell12431 ⟨4, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (83940048449097 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1142980325417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_5 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (10488135741293 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457192933993 / 20000000000000 : ℝ))
      (E := (cell12431 ⟨5, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (10488135741293 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457192933993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_6 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (41935074161939 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571492164827 / 25000000000000 : ℝ))
      (E := (cell12431 ⟨6, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (41935074161939 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571492164827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_7 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (83835235593691 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1142986313573 / 50000000000000 : ℝ))
      (E := (cell12431 ⟨7, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (83835235593691 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1142986313573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_8 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (41900173851983 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1142988319737 / 50000000000000 : ℝ))
      (E := (cell12431 ⟨8, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (41900173851983 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1142988319737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_9 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (3350619384763 / 4000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285980646141 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨9, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (3350619384763 / 4000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285980646141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_10 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (3349225852143 / 4000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285984596649 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨10, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (3349225852143 / 4000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285984596649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_11 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (2615494772569 / 3125000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285988614273 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨11, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (2615494772569 / 3125000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2285988614273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_12 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (41830521919951 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1142996294987 / 50000000000000 : ℝ))
      (E := (cell12431 ⟨12, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (41830521919951 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1142996294987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_13 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (83626279621767 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571499147133 / 25000000000000 : ℝ))
      (E := (cell12431 ⟨13, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (83626279621767 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571499147133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_14 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (10448942504137 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457200123293 / 20000000000000 : ℝ))
      (E := (cell12431 ⟨14, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (10448942504137 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457200123293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_15 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (41778412519681 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286004621909 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨15, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (41778412519681 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286004621909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_16 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (83522134606219 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286008610813 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨16, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (83522134606219 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286008610813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_17 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (10435933587437 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286012588889 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨17, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (10435933587437 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286012588889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_18 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (20863206821301 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (11430083099 / 500000000000 : ℝ))
      (E := (cell12431 ⟨18, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (20863206821301 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (11430083099 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_19 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (41709105164763 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (8929767939 / 390625000000 : ℝ))
      (E := (cell12431 ⟨19, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (41709105164763 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (8929767939 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12432_0 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (84080132583051 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285810103221 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨0, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (84080132583051 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285810103221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_1 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (42022535191037 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285814105889 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨1, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (42022535191037 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285814105889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_2 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (84010033238859 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142909050747 / 50000000000000 : ℝ))
      (E := (cell12432 ⟨2, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (84010033238859 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142909050747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_3 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (83975021116629 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (71431940607 / 3125000000000 : ℝ))
      (E := (cell12432 ⟨3, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (83975021116629 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (71431940607 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_4 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (16788006795761 / 20000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285826108801 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨4, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (16788006795761 / 20000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285826108801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_5 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41952535894499 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285830080593 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨5, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41952535894499 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285830080593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_6 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (20967533627753 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142917040631 / 50000000000000 : ℝ))
      (E := (cell12432 ⟨6, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (20967533627753 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142917040631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_7 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41917611054421 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571459529789 / 25000000000000 : ℝ))
      (E := (cell12432 ⟨7, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41917611054421 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571459529789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_8 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (5237520909167 / 6250000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (71432565201 / 3125000000000 : ℝ))
      (E := (cell12432 ⟨8, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (5237520909167 / 6250000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (71432565201 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_9 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (83765471788873 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142923053389 / 50000000000000 : ℝ))
      (E := (cell12432 ⟨9, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (83765471788873 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142923053389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_10 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (83730633800003 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571462517937 / 25000000000000 : ℝ))
      (E := (cell12432 ⟨10, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (83730633800003 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571462517937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_11 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (10461977568101 / 12500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (91434161863 / 4000000000000 : ℝ))
      (E := (cell12432 ⟨11, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (10461977568101 / 12500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (91434161863 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_12 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41830515994107 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285858096339 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨12, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41830515994107 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285858096339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_13 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41813134047667 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142931026807 / 50000000000000 : ℝ))
      (E := (cell12432 ⟨13, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41813134047667 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1142931026807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_14 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (4179576441573 / 5000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571466510249 / 25000000000000 : ℝ))
      (E := (cell12432 ⟨14, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (4179576441573 / 5000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571466510249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_15 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (20889203540517 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (142866879047 / 6250000000000 : ℝ))
      (E := (cell12432 ⟨15, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (20889203540517 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (142866879047 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_16 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (8352212405281 / 10000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285874072749 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨16, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (8352212405281 / 10000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285874072749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_17 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (1043593230869 / 1250000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285878070691 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨17, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (1043593230869 / 1250000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285878070691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_18 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (83452817378207 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (57147051601 / 2500000000000 : ℝ))
      (E := (cell12432 ⟨18, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (83452817378207 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (57147051601 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_19 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (2606818773283 / 3125000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285886058017 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨19, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (2606818773283 / 3125000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285886058017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12433_0 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (1681602335897 / 2000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (571418909329 / 25000000000000 : ℝ))
      (E := (cell12433 ⟨0, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (1681602335897 / 2000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (571418909329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_1 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (10505631865581 / 12500000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285679647477 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨1, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (10505631865581 / 12500000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285679647477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_2 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (42005009055869 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (285710456421 / 12500000000000 : ℝ))
      (E := (cell12433 ⟨2, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (42005009055869 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (285710456421 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_3 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41987503159673 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142843800259 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨3, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41987503159673 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142843800259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_4 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (20985004877723 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457138323947 / 20000000000000 : ℝ))
      (E := (cell12433 ⟨4, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (20985004877723 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457138323947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_5 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (8390505764999 / 10000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142847801077 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨5, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (8390505764999 / 10000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142847801077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_6 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (20967530175111 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (571424903559 / 25000000000000 : ℝ))
      (E := (cell12433 ⟨6, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (20967530175111 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (571424903559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_7 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (67068166901 / 80000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285703606383 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨7, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (67068166901 / 80000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285703606383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_8 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83800321391593 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (114285379331 / 5000000000000 : ℝ))
      (E := (cell12433 ⟨8, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83800321391593 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (114285379331 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_9 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41882729480423 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285711620709 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨9, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41882729480423 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285711620709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_10 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83730621298567 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (571428900051 / 25000000000000 : ℝ))
      (E := (cell12433 ⟨10, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83730621298567 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (571428900051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_11 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41847904184751 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (114285979517 / 5000000000000 : ℝ))
      (E := (cell12433 ⟨11, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41847904184751 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (114285979517 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_12 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (4183051006929 / 5000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (228572359813 / 10000000000000 : ℝ))
      (E := (cell12433 ⟨12, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (4183051006929 / 5000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (228572359813 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_13 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41813128285457 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (9142910289 / 400000000000 : ℝ))
      (E := (cell12433 ⟨13, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41813128285457 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (9142910289 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_14 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41795758815899 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457146315451 / 20000000000000 : ℝ))
      (E := (cell12433 ⟨14, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41795758815899 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457146315451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_15 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41778401643353 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (7142923629 / 312500000000 : ℝ))
      (E := (cell12433 ⟨15, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41778401643353 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (7142923629 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_16 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (16704422700259 / 20000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (142858724277 / 6250000000000 : ℝ))
      (E := (cell12433 ⟨16, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (16704422700259 / 20000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (142858724277 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_17 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83487448241397 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (571435887031 / 25000000000000 : ℝ))
      (E := (cell12433 ⟨17, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83487448241397 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (571435887031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_18 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41726403736511 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142873781079 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨18, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41726403736511 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142873781079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_19 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (83418191162357 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285751577593 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨19, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (83418191162357 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285751577593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12434_0 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (84080101009191 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285541224119 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨0, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (84080101009191 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285541224119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_1 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (84045039469723 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142772592017 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨1, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (84045039469723 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142772592017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_2 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (84010002987077 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285549196251 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨2, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (84010002987077 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285549196251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_3 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41987495762241 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (228555321237 / 10000000000000 : ℝ))
      (E := (cell12434 ⟨3, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41987495762241 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (228555321237 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_4 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41970002522679 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285557183639 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨4, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41970002522679 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285557183639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_5 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83905043513319 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (142847573547 / 6250000000000 : ℝ))
      (E := (cell12434 ⟨5, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83905043513319 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (142847573547 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_6 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83870106892173 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285565200311 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨6, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83870106892173 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285565200311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_7 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41917597572957 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285569146777 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨7, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41917597572957 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285569146777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_8 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (8380030823873 / 10000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (285696649751 / 12500000000000 : ℝ))
      (E := (cell12434 ⟨8, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (8380030823873 / 10000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (285696649751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_9 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83765446134993 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285577187937 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨9, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83765446134993 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285577187937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_10 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (16746121759853 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285581182023 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨10, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (16746121759853 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285581182023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_11 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (8369579619629 / 10000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571396282373 / 25000000000000 : ℝ))
      (E := (cell12434 ⟨11, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (8369579619629 / 10000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571396282373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_12 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83661008291 / 100000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571397288353 / 25000000000000 : ℝ))
      (E := (cell12434 ⟨12, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83661008291 / 100000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571397288353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_13 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83626245048507 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142796572221 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨13, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83626245048507 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142796572221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_14 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (20897876608527 / 25000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (71424911473 / 3125000000000 : ℝ))
      (E := (cell12434 ⟨14, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (20897876608527 / 25000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (71424911473 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_15 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83556792413277 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571400292407 / 25000000000000 : ℝ))
      (E := (cell12434 ⟨15, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83556792413277 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571400292407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_16 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (10440262868959 / 12500000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142802578933 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨16, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (10440262868959 / 12500000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142802578933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_17 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (667899504121 / 800000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (457121827511 / 20000000000000 : ℝ))
      (E := (cell12434 ⟨17, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (667899504121 / 800000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (457121827511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_18 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83452797569649 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571403278539 / 25000000000000 : ℝ))
      (E := (cell12434 ⟨18, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83452797569649 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571403278539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_19 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (83418181581431 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285617151113 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨19, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (83418181581431 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285617151113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12435_0 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (3363203409043 / 4000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (285675850731 / 12500000000000 : ℝ))
      (E := (cell12435 ⟨0, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (3363203409043 / 4000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (285675850731 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_1 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (84045024017299 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285410831171 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨1, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (84045024017299 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285410831171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_2 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (84009987864877 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571353712951 / 25000000000000 : ℝ))
      (E := (cell12435 ⟨2, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (84009987864877 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571353712951 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_3 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (83974976732037 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571354704819 / 25000000000000 : ℝ))
      (E := (cell12435 ⟨3, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (83974976732037 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571354704819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_4 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41969995291101 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457084560103 / 20000000000000 : ℝ))
      (E := (cell12435 ⟨4, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41969995291101 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457084560103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_5 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41952514689493 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142713402193 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨5, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41952514689493 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142713402193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_6 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41935046543099 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285430781567 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨6, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41935046543099 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285430781567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_7 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (16767036333567 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285434798283 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨7, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (16767036333567 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285434798283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_8 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41900147544041 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (114271940233 / 5000000000000 : ℝ))
      (E := (cell12435 ⟨8, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41900147544041 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (114271940233 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_9 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (20941358327829 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142721404231 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨9, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (20941358327829 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142721404231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_10 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (83730596302097 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571361689797 / 25000000000000 : ℝ))
      (E := (cell12435 ⟨10, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (83730596302097 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571361689797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_11 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (20923946006293 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (142840673757 / 6250000000000 : ℝ))
      (E := (cell12435 ⟨11, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (20923946006293 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (142840673757 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_12 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (83660996445473 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285454762187 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨12, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (83660996445473 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285454762187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_13 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (83626233528113 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285458770193 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨13, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (83626233528113 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285458770193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_14 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (8359149523839 / 10000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (228546275253 / 10000000000000 : ℝ))
      (E := (cell12435 ⟨14, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (8359149523839 / 10000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (228546275253 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_15 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (4177839077089 / 5000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (228546677353 / 10000000000000 : ℝ))
      (E := (cell12435 ⟨15, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (4177839077089 / 5000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (228546677353 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_16 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (4176104620197 / 5000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285470781053 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨16, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (4176104620197 / 5000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285470781053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_17 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (16697485558141 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285474780803 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨17, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (16697485558141 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285474780803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_18 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (10431598458511 / 12500000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (3571060591 / 156250000000 : ℝ))
      (E := (cell12435 ⟨18, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (10431598458511 / 12500000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (3571060591 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_19 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (20854543000569 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285482778579 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨19, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (20854543000569 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285482778579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12436_0 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (84080069445501 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (571318124517 / 25000000000000 : ℝ))
      (E := (cell12436 ⟨0, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (84080069445501 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (571318124517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_1 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (5252813035461 / 6250000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142638265541 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨1, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (5252813035461 / 6250000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142638265541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_2 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (5250623296571 / 6250000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (71415015699 / 3125000000000 : ℝ))
      (E := (cell12436 ⟨2, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (5250623296571 / 6250000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (71415015699 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_3 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83974961942011 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285284479087 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨3, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83974961942011 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285284479087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_4 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83939976121423 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285288470363 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨4, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83939976121423 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285288470363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_5 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (8390501524699 / 10000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457058497011 / 20000000000000 : ℝ))
      (E := (cell12436 ⟨5, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (8390501524699 / 10000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457058497011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_6 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (2096751982063 / 2500000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457059294769 / 20000000000000 : ℝ))
      (E := (cell12436 ⟨6, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (2096751982063 / 2500000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457059294769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_7 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (8383516819201 / 10000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142650251479 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨7, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (8383516819201 / 10000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142650251479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_8 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83800281939649 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285304464543 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨8, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83800281939649 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285304464543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_9 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (20941355122453 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457061696457 / 20000000000000 : ℝ))
      (E := (cell12436 ⟨9, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (20941355122453 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (457061696457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_10 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41865291903531 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285312447733 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨10, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41865291903531 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285312447733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_11 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83695771856147 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285316484159 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨11, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83695771856147 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285316484159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_12 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41830492300999 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142660241259 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨12, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41830492300999 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142660241259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_13 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (20906555502433 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285324449499 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨13, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (20906555502433 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285324449499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_14 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (20897871011161 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (285666056207 / 12500000000000 : ℝ))
      (E := (cell12436 ⟨14, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (20897871011161 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (285666056207 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_15 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (16711354134443 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142666215559 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨15, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (16711354134443 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142666215559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_16 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (835220818581 / 1000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285336457991 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨16, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (835220818581 / 1000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285336457991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_17 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83487417568137 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142670209843 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨17, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83487417568137 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142670209843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_18 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41726388884169 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142672219 / 50000000000 : ℝ))
      (E := (cell12436 ⟨18, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41726388884169 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142672219 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_19 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (83418162424893 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285348459991 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨19, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (83418162424893 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285348459991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12437_0 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (21020013416867 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285138243001 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨0, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (21020013416867 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285138243001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_1 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (84044993119953 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142571112983 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨1, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (84044993119953 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142571112983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_2 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (42004978813927 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457029252721 / 20000000000000 : ℝ))
      (E := (cell12437 ⟨2, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (42004978813927 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457029252721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_3 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41987473577201 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285150249661 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨3, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41987473577201 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285150249661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_4 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41969980831511 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285154251061 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨4, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41969980831511 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285154251061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_5 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (8390500111733 / 10000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142579109383 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨5, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (8390500111733 / 10000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142579109383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_6 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (5241879092571 / 6250000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285162219231 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨6, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (5241879092571 / 6250000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285162219231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_7 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (2095878867961 / 2500000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285645775357 / 12500000000000 : ℝ))
      (E := (cell12437 ⟨7, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (2095878867961 / 2500000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285645775357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_8 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (83800268793429 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285170235633 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨8, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (83800268793429 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285170235633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_9 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41882703835241 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (17852923511 / 781250000000 : ℝ))
      (E := (cell12437 ⟨9, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41882703835241 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (17852923511 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_10 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (1046632141427 / 1250000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571294547411 / 25000000000000 : ℝ))
      (E := (cell12437 ⟨10, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (1046632141427 / 1250000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571294547411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_11 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (83695759689213 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285182183599 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨11, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (83695759689213 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285182183599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_12 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (3346438910423 / 4000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142593099141 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨12, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (3346438910423 / 4000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142593099141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_13 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (83626210493361 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (71412193199 / 3125000000000 : ℝ))
      (E := (cell12437 ⟨13, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (83626210493361 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (71412193199 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_14 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (8359147285287 / 10000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285649275051 / 12500000000000 : ℝ))
      (E := (cell12437 ⟨14, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (8359147285287 / 10000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285649275051 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_15 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (4177837990229 / 5000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285198200531 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨15, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (4177837990229 / 5000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285198200531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_16 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (83522071314151 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571300547171 / 25000000000000 : ℝ))
      (E := (cell12437 ⟨16, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (83522071314151 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (571300547171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_17 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (83487407347419 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (228520617057 / 10000000000000 : ℝ))
      (E := (cell12437 ⟨17, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (83487407347419 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (228520617057 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_18 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41726383935199 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457042030329 / 20000000000000 : ℝ))
      (E := (cell12437 ⟨18, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41726383935199 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (457042030329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_19 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (130340863827 / 156250000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285651774419 / 12500000000000 : ℝ))
      (E := (cell12437 ⟨19, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (130340863827 / 156250000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285651774419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12438_0 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (3363201515679 / 4000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285004040647 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨0, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (3363201515679 / 4000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285004040647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_1 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (84044977675029 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457001606287 / 20000000000000 : ℝ))
      (E := (cell12438 ⟨1, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (84044977675029 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457001606287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_2 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (8400994251303 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285012019857 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨2, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (8400994251303 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285012019857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_3 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83974932369211 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (571254003823 / 25000000000000 : ℝ))
      (E := (cell12438 ⟨3, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83974932369211 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (571254003823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_4 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83939947206997 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142510013429 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨4, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83939947206997 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142510013429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_5 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41952493495003 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (571256001379 / 25000000000000 : ℝ))
      (E := (cell12438 ⟨5, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41952493495003 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (571256001379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_6 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (327617389383 / 390625000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142514008861 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨6, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (327617389383 / 390625000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142514008861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_7 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20958785311781 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285032013873 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨7, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20958785311781 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285032013873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_8 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83800255649423 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285036001989 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨8, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83800255649423 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285036001989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_9 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20941348713331 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142519994917 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨9, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20941348713331 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142519994917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_10 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (8373055882339 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285043984921 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨10, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (8373055882339 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285043984921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_11 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20923936881093 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285047994509 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨11, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20923936881093 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285047994509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_12 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20915240230301 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142525983771 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨12, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20915240230301 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142525983771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_13 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41813099489501 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142527984399 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨13, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41813099489501 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142527984399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_14 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41795730831533 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285060004787 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨14, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41795730831533 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285060004787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_15 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20889187234719 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142531982751 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨15, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20889187234719 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142531982751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_16 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20880515193023 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142533986567 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨16, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20880515193023 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142533986567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_17 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (10435924641069 / 12500000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142535987637 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨17, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (10435924641069 / 12500000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142535987637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_18 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83452757974269 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (114253798869 / 5000000000000 : ℝ))
      (E := (cell12438 ⟨18, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83452757974269 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (114253798869 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_19 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (83418143275437 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285079984663 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨19, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (83418143275437 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285079984663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12439_0 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (42040011059511 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (35701092047 / 1562500000000 : ℝ))
      (E := (cell12439 ⟨0, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (42040011059511 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (35701092047 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_1 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (21011240558151 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571218472421 / 25000000000000 : ℝ))
      (E := (cell12439 ⟨1, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (21011240558151 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571218472421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_2 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (10501240925083 / 12500000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (35701216981 / 1562500000000 : ℝ))
      (E := (cell12439 ⟨2, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (10501240925083 / 12500000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (35701216981 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_3 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83974917586437 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142440945843 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨3, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83974917586437 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142440945843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_4 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (20984983188337 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (142805365977 / 6250000000000 : ℝ))
      (E := (cell12439 ⟨4, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (20984983188337 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (142805365977 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_5 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (10488121608127 / 12500000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (228488984531 / 10000000000000 : ℝ))
      (E := (cell12439 ⟨5, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (10488121608127 / 12500000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (228488984531 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_6 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41935018942627 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284893869321 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨6, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41935018942627 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284893869321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_7 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83835127778061 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284897878063 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨7, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83835127778061 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284897878063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_8 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (8380024250763 / 10000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284901879553 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨8, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (8380024250763 / 10000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284901879553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_9 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83765382038339 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284905823563 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨9, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83765382038339 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284905823563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_10 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83730546334753 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142454916783 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨10, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83730546334753 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142454916783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_11 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41847867680811 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284913858853 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨11, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41847867680811 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284913858853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_12 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83660949083883 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (456983569673 / 20000000000000 : ℝ))
      (E := (cell12439 ⟨12, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83660949083883 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (456983569673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_13 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83626187466653 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284921808791 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨13, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83626187466653 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284921808791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_14 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83591450475233 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284925804681 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨14, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83591450475233 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284925804681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_15 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83556738075103 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142464921149 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨15, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83556738075103 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142464921149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_16 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (83522050231923 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284933811341 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨16, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (83522050231923 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2284933811341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_17 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41743693455767 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (11424689169 / 500000000000 : ℝ))
      (E := (cell12439 ⟨17, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41743693455767 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (11424689169 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_18 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (1669054961599 / 2000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571235449699 / 25000000000000 : ℝ))
      (E := (cell12439 ⟨18, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (1669054961599 / 2000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571235449699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_19 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (20854533425841 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571236456981 / 25000000000000 : ℝ))
      (E := (cell12439 ⟨19, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (20854533425841 / 25000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571236456981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12440_0 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (1313750099197 / 1562500000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456947158817 / 20000000000000 : ℝ))
      (E := (cell12440 ⟨0, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (1313750099197 / 1562500000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456947158817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_1 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (21011236698169 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571184950179 / 25000000000000 : ℝ))
      (E := (cell12440 ⟨1, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (21011236698169 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571184950179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_2 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (21002478072689 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284743806559 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨2, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (21002478072689 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284743806559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_3 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83974902806079 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284747763141 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨3, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83974902806079 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284747763141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_4 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41969959151037 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284751795261 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨4, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41969959151037 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284751795261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_5 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83904958742361 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284755796047 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨5, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83904958742361 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284755796047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_6 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83870024090753 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284759774029 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨6, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83870024090753 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284759774029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_7 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (20958778577813 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284763737479 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨7, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (20958778577813 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284763737479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_8 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (1676004587361 / 2000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142383876193 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨8, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (1676004587361 / 2000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142383876193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_9 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (3350614769021 / 4000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (228477176859 / 10000000000000 : ℝ))
      (E := (cell12440 ⟨9, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (3350614769021 / 4000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (228477176859 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_10 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41865266924123 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284775735581 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨10, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41865266924123 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284775735581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_11 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83695723200963 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284779776631 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨11, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83695723200963 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284779776631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_12 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83660937248613 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284783724623 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨12, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83660937248613 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284783724623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_13 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41813087978157 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284787760437 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨13, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41813087978157 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284787760437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_14 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83591439289369 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284791716317 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨14, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83591439289369 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284791716317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_15 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41778363606629 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456959142931 / 20000000000000 : ℝ))
      (E := (cell12440 ⟨15, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41778363606629 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456959142931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_16 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (20880509923411 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456959940661 / 20000000000000 : ℝ))
      (E := (cell12440 ⟨16, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (20880509923411 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (456959940661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_17 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (16697475339273 / 20000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284803746151 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨17, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (16697475339273 / 20000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284803746151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_18 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (1043159227343 / 1250000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (142800483269 / 6250000000000 : ℝ))
      (E := (cell12440 ⟨18, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (1043159227343 / 1250000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (142800483269 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_19 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (83418124133061 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284811725137 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨19, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (83418124133061 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284811725137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12441_0 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (84079990580733 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284601749881 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨0, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (84079990580733 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284601749881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_1 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (84044931355247 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (228460576453 / 10000000000000 : ℝ))
      (E := (cell12441 ⟨1, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (84044931355247 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (228460576453 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_2 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (84009897183303 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142304860677 / 50000000000000 : ℝ))
      (E := (cell12441 ⟨2, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (84009897183303 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142304860677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_3 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (10496861003517 / 12500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571153436341 / 25000000000000 : ℝ))
      (E := (cell12441 ⟨3, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (10496861003517 / 12500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571153436341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_4 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (3357596154127 / 4000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284617729993 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨4, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (3357596154127 / 4000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284617729993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_5 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (2097623615551 / 2500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (228462174193 / 10000000000000 : ℝ))
      (E := (cell12441 ⟨5, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (2097623615551 / 2500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (228462174193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_6 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41935005149273 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284625731847 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨6, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41935005149273 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284625731847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_7 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (16767020169339 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284629708019 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨7, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (16767020169339 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284629708019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_8 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83800216230681 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284633736431 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨8, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83800216230681 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284633736431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_9 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83765356414883 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284637708929 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨9, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83765356414883 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284637708929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_10 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (8373052136387 / 10000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285580211371 / 12500000000000 : ℝ))
      (E := (cell12441 ⟨10, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (8373052136387 / 10000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285580211371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_11 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41847855521197 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456929137961 / 20000000000000 : ℝ))
      (E := (cell12441 ⟨11, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41847855521197 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456929137961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_12 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (2614403919231 / 3125000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284649712447 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨12, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (2614403919231 / 3125000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284649712447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_13 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (16725232889597 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (57116342689 / 2500000000000 : ℝ))
      (E := (cell12441 ⟨13, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (16725232889597 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (57116342689 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_14 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (3343657124219 / 4000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284657681583 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨14, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (3343657124219 / 4000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284657681583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_15 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83556716353343 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142330849421 / 50000000000000 : ℝ))
      (E := (cell12441 ⟨15, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83556716353343 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142330849421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_16 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83522029157253 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (228466570719 / 10000000000000 : ℝ))
      (E := (cell12441 ⟨16, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83522029157253 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (228466570719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_17 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41743683241523 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (91386788493 / 4000000000000 : ℝ))
      (E := (cell12441 ⟨17, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41743683241523 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (91386788493 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_18 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (83452728296739 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142336830749 / 50000000000000 : ℝ))
      (E := (cell12441 ⟨18, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (83452728296739 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142336830749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_19 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41709057282263 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456935535261 / 20000000000000 : ℝ))
      (E := (cell12441 ⟨19, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41709057282263 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (456935535261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12442_0 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (21019993703849 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (456893551679 / 20000000000000 : ℝ))
      (E := (cell12442 ⟨0, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (21019993703849 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (456893551679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_1 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (42022457960157 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (228447178113 / 10000000000000 : ℝ))
      (E := (cell12442 ⟨1, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (42022457960157 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (228447178113 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_2 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (84009882078307 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571118936707 / 25000000000000 : ℝ))
      (E := (cell12442 ⟨2, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (84009882078307 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571118936707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_3 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83974873252609 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142239890251 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨3, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83974873252609 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142239890251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_4 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (1678797788133 / 2000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (71390117987 / 3125000000000 : ℝ))
      (E := (cell12442 ⟨4, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (1678797788133 / 2000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (71390117987 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_5 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83904930504053 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142243870429 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨5, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83904930504053 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142243870429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_6 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83869996508631 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142245871389 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨6, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83869996508631 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142245871389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_7 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (8383508738439 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285561966467 / 12500000000000 : ℝ))
      (E := (cell12442 ⟨7, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (8383508738439 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285561966467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_8 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83800203095523 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571124928937 / 25000000000000 : ℝ))
      (E := (cell12442 ⟨8, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83800203095523 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571124928937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_9 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (20941335901603 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (228450376057 / 10000000000000 : ℝ))
      (E := (cell12442 ⟨9, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (20941335901603 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (228450376057 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_10 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (10466313610203 / 12500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (142781731233 / 6250000000000 : ℝ))
      (E := (cell12442 ⟨10, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (10466313610203 / 12500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (142781731233 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_11 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (16739139777183 / 20000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142255857229 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨11, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (16739139777183 / 20000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142255857229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_12 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (41830456792111 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284515695707 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨12, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (41830456792111 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284515695707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_13 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (16725230588333 / 20000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284519708251 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨13, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (16725230588333 / 20000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284519708251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_14 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83591416923549 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142261850241 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨14, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83591416923549 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142261850241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_15 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (20889176373839 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142263868363 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨15, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (20889176373839 / 25000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142263868363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_16 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (83522018622751 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571132926669 / 25000000000000 : ℝ))
      (E := (cell12442 ⟨16, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (83522018622751 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571132926669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_17 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (3339494250863 / 4000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (71391739817 / 3125000000000 : ℝ))
      (E := (cell12442 ⟨17, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (3339494250863 / 4000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (71391739817 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_18 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (41726359203923 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284539702787 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨18, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (41726359203923 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284539702787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_19 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (130340789059 / 156250000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571135920357 / 25000000000000 : ℝ))
      (E := (cell12442 ⟨19, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (130340789059 / 156250000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571135920357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12443_0 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (21019989763149 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (142770863727 / 6250000000000 : ℝ))
      (E := (cell12443 ⟨0, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (21019989763149 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (142770863727 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_1 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (42022450243939 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284337850517 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨1, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (42022450243939 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284337850517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_2 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (42004933487883 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456868365031 / 20000000000000 : ℝ))
      (E := (cell12443 ⟨2, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (42004933487883 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456868365031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_3 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (10496857309937 / 12500000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456869162141 / 20000000000000 : ℝ))
      (E := (cell12443 ⟨3, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (10496857309937 / 12500000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456869162141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_4 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41969937481249 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284349816281 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨4, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41969937481249 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284349816281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_5 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83904916388397 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284353792837 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨5, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83904916388397 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284353792837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_6 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (5241873920063 / 6250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284357806823 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨6, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (5241873920063 / 6250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284357806823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_7 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (5239692120271 / 6250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285545226079 / 12500000000000 : ℝ))
      (E := (cell12443 ⟨7, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (5239692120271 / 6250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285545226079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_8 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (5237511872661 / 6250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (57109145157 / 2500000000000 : ℝ))
      (E := (cell12443 ⟨8, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (5237511872661 / 6250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (57109145157 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_9 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (8376533080011 / 10000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284369807527 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨9, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (8376533080011 / 10000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284369807527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_10 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (20932624100377 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284373819879 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨10, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (20932624100377 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284373819879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_11 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (3347827469261 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284377792549 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨11, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (3347827469261 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284377792549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_12 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83660901755099 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284381790539 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨12, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83660901755099 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284381790539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_13 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41813070718677 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (228438576251 / 10000000000000 : ℝ))
      (E := (cell12443 ⟨13, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41813070718677 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (228438576251 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_14 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (10448925717949 / 12500000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142194886507 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨14, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (10448925717949 / 12500000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142194886507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_15 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41778347319649 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (571098442543 / 25000000000000 : ℝ))
      (E := (cell12443 ⟨15, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41778347319649 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (571098442543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_16 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83522008090137 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142198879963 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨16, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83522008090137 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142198879963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_17 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83487346061951 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284401747973 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨17, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83487346061951 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284401747973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_18 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (83452708520761 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (142775362373 / 6250000000000 : ℝ))
      (E := (cell12443 ⟨18, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (83452708520761 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (142775362373 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_19 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41709047716381 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284409740507 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨19, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41709047716381 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284409740507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12444_0 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (84079943292333 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571049997843 / 25000000000000 : ℝ))
      (E := (cell12444 ⟨0, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (84079943292333 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571049997843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_1 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (84044885057937 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284203972691 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨1, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (84044885057937 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284203972691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_2 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (84009851875679 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (456841591267 / 20000000000000 : ℝ))
      (E := (cell12444 ⟨2, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (84009851875679 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (456841591267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_3 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (20993710927199 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (7138162349 / 312500000000 : ℝ))
      (E := (cell12444 ⟨3, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (20993710927199 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (7138162349 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_4 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (1049248256509 / 1250000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142107983919 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨4, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (1049248256509 / 1250000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142107983919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_5 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (3356196091003 / 4000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284219955763 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨5, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (3356196091003 / 4000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284219955763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_6 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83869968935677 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284223923981 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨6, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83869968935677 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284223923981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_7 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83835060466533 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284227938707 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨7, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83835060466533 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284227938707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_8 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83800176831839 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285528993757 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨8, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83800176831839 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285528993757 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_9 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41882658997989 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (142764744237 / 6250000000000 : ℝ))
      (E := (cell12444 ⟨9, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41882658997989 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (142764744237 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_10 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83730483923521 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142119967693 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨10, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83730483923521 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142119967693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_11 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (10461959322403 / 12500000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (28553049051 / 1250000000000 : ℝ))
      (E := (cell12444 ⟨11, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (10461959322403 / 12500000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (28553049051 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_12 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41830444964013 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285530992359 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨12, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41830444964013 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285530992359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_13 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (1672522598701 / 2000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571062982107 / 25000000000000 : ℝ))
      (E := (cell12444 ⟨13, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (1672522598701 / 2000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571062982107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_14 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41795697282801 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (114212794959 / 5000000000000 : ℝ))
      (E := (cell12444 ⟨14, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41795697282801 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (114212794959 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_15 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83556683785167 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284259915453 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨15, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83556683785167 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284259915453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_16 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (8352199755941 / 10000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142131962549 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨16, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (8352199755941 / 10000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142131962549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_17 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (3339493434167 / 4000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284267875629 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨17, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (3339493434167 / 4000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284267875629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_18 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83452698635483 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284271888837 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨18, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83452698635483 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284271888837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_19 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (83418085869531 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571068977943 / 25000000000000 : ℝ))
      (E := (cell12444 ⟨19, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (83418085869531 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571068977943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12445_0 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (42039963767303 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456813231611 / 20000000000000 : ℝ))
      (E := (cell12445 ⟨0, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (42039963767303 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456813231611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_1 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (21011217407623 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142035073827 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨1, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (21011217407623 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142035073827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_2 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (84009836778047 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284074140371 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨2, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (84009836778047 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284074140371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_3 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (8397482894051 / 10000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (285509768197 / 12500000000000 : ℝ))
      (E := (cell12445 ⟨3, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (8397482894051 / 10000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (285509768197 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_4 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41969923040657 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456816422901 / 20000000000000 : ℝ))
      (E := (cell12445 ⟨4, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41969923040657 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456816422901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_5 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83904888164083 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142043056921 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨5, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83904888164083 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142043056921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_6 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (20967488788159 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284090094257 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨6, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (20967488788159 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284090094257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_7 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (4191752350549 / 5000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142047060983 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨7, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (4191752350549 / 5000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142047060983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_8 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (5237510231457 / 6250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284098089109 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨8, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (5237510231457 / 6250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284098089109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_9 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (2617665787313 / 3125000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571025529841 / 25000000000000 : ℝ))
      (E := (cell12445 ⟨9, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (2617665787313 / 3125000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571025529841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_10 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83730471447663 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (142756631517 / 6250000000000 : ℝ))
      (E := (cell12445 ⟨10, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83730471447663 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (142756631517 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_11 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83695662429011 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142055054527 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨11, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83695662429011 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142055054527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_12 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83660878103 / 100000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284114082649 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨12, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83660878103 / 100000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284114082649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_13 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41813059217377 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284118089829 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨13, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41813059217377 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284118089829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_14 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (4179569169479 / 5000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284122078983 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨14, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (4179569169479 / 5000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284122078983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_15 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83556672932963 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571031528609 / 25000000000000 : ℝ))
      (E := (cell12445 ⟨15, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83556672932963 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571031528609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_16 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83521987030571 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284130085877 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨16, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83521987030571 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284130085877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_17 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83487325648247 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456826811423 / 20000000000000 : ℝ))
      (E := (cell12445 ⟨17, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83487325648247 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456826811423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_18 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83452688752013 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142069045903 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨18, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83452688752013 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142069045903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_19 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (83418076308067 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (142758879923 / 6250000000000 : ℝ))
      (E := (cell12445 ⟨19, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (83418076308067 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (142758879923 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12446_0 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (42039955889707 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283932377463 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨0, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (42039955889707 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283932377463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_1 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (84044854205541 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283936375409 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨1, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (84044854205541 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283936375409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_2 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (21002455420717 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283940377263 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨2, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (21002455420717 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283940377263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_3 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (20993703543659 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456788878479 / 20000000000000 : ℝ))
      (E := (cell12446 ⟨3, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (20993703543659 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456788878479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_4 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83939831644279 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283948372037 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨4, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83939831644279 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283948372037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_5 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83904874055423 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283952382873 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨5, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83904874055423 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283952382873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_6 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41934970685943 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1141978187787 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨6, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41934970685943 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1141978187787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_7 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83835033557677 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1141980179203 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨7, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83835033557677 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1141980179203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_8 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83800150576993 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283964339381 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨8, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83800150576993 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283964339381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_9 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83765292394221 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (142748020391 / 6250000000000 : ℝ))
      (E := (cell12446 ⟨9, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83765292394221 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (142748020391 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_10 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83730458973933 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456794465307 / 20000000000000 : ℝ))
      (E := (cell12446 ⟨10, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83730458973933 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456794465307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_11 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (16739130056177 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283976347471 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨11, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (16739130056177 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2283976347471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_12 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83660866280021 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1141990169 / 50000000000 : ℝ))
      (E := (cell12446 ⟨12, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83660866280021 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1141990169 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_13 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (16725221387293 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1141992152401 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨13, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (16725221387293 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1141992152401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_14 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (20897843053881 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (285498539053 / 12500000000000 : ℝ))
      (E := (cell12446 ⟨14, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (20897843053881 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (285498539053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_15 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41778331041343 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456798461797 / 20000000000000 : ℝ))
      (E := (cell12446 ⟨15, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41778331041343 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456798461797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_16 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83521976503617 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (285499537553 / 12500000000000 : ℝ))
      (E := (cell12446 ⟨16, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83521976503617 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (285499537553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_17 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (20871828861041 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142000146217 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨17, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (20871828861041 / 25000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142000146217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_18 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (83452678870349 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456800858093 / 20000000000000 : ℝ))
      (E := (cell12446 ⟨18, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (83452678870349 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (456800858093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_19 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (8341806674837 / 10000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (571002074931 / 25000000000000 : ℝ))
      (E := (cell12446 ⟨19, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (8341806674837 / 10000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (571002074931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12447_0 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (42039948013379 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283798649597 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨0, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (42039948013379 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283798649597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_1 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (84044838783083 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141901327979 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨1, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (84044838783083 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141901327979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_2 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (42004903295071 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141903333507 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨2, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (42004903295071 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141903333507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_3 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (3358991976447 / 4000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141905317141 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨3, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (3358991976447 / 4000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141905317141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_4 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (5246238575601 / 6250000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141907341279 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨4, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (5246238575601 / 6250000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141907341279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_5 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83904859949093 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283818647059 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨5, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83904859949093 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283818647059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_6 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (3354797103737 / 4000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (285477831511 / 12500000000000 : ℝ))
      (E := (cell12447 ⟨6, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (3354797103737 / 4000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (285477831511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_7 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83835020106623 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (71369582751 / 3125000000000 : ℝ))
      (E := (cell12447 ⟨7, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83835020106623 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (71369582751 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_8 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (20950034363221 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283830642903 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨8, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (20950034363221 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283830642903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_9 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16753055919319 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283834644457 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨9, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16753055919319 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283834644457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_10 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (8373044650233 / 10000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283838660197 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨10, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (8373044650233 / 10000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283838660197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_11 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83695638134847 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283842639333 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨11, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83695638134847 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283842639333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_12 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83660854459089 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (114192332343 / 5000000000000 : ℝ))
      (E := (cell12447 ⟨12, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83660854459089 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (114192332343 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_13 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83626095440183 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283850631439 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨13, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83626095440183 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283850631439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_14 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16718272208687 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (456770919901 / 20000000000000 : ℝ))
      (E := (cell12447 ⟨14, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16718272208687 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (456770919901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_15 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16711330246867 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141929307687 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨15, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16711330246867 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141929307687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_16 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (1670439319571 / 2000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141931313449 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨16, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (1670439319571 / 2000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141931313449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_17 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (10435913155241 / 12500000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141933290793 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨17, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (10435913155241 / 12500000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141933290793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_18 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83452668990491 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283870601229 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨18, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83452668990491 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283870601229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_19 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (83418057190439 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283874574643 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨19, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (83418057190439 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283874574643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12448_0 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (16815976055327 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570916258061 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨0, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (16815976055327 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570916258061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_1 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (84044823363119 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283668989299 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨1, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (84044823363119 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283668989299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_2 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (84009791499869 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283673009623 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨2, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (84009791499869 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283673009623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_3 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (671798277201 / 800000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570919246737 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨3, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (671798277201 / 800000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570919246737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_4 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83939802777323 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283680988191 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨4, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83939802777323 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283680988191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_5 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83904845845093 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (11418425111 / 500000000000 : ℝ))
      (E := (cell12448 ⟨5, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83904845845093 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (11418425111 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_6 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41934956908627 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283688981721 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨6, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41934956908627 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283688981721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_7 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83835006657817 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283692990843 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨7, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83835006657817 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283692990843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_8 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41900062165491 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (91347879987 / 4000000000000 : ℝ))
      (E := (cell12448 ⟨8, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41900062165491 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (91347879987 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_9 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (5235329175071 / 6250000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283700957979 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨9, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (5235329175071 / 6250000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283700957979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_10 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41865217016427 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283704989221 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨10, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41865217016427 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283704989221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_11 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (16739125198179 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (7136590577 / 312500000000 : ℝ))
      (E := (cell12448 ⟨11, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (16739125198179 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (7136590577 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_12 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (20915210660051 / 25000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570928237791 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨12, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (20915210660051 / 25000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570928237791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_13 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41813041972953 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283716953563 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨13, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41813041972953 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283716953563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_14 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (2612229683541 / 3125000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (35683139691 / 1562500000000 : ℝ))
      (E := (cell12448 ⟨14, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (2612229683541 / 3125000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (35683139691 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_15 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (8355664038791 / 10000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283724975467 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨15, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (8355664038791 / 10000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283724975467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_16 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83521955455369 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141864474491 / 50000000000000 : ℝ))
      (E := (cell12448 ⟨16, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83521955455369 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141864474491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_17 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83487295041537 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283732924571 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨17, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83487295041537 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283732924571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_18 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41726329556219 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (228373696589 / 10000000000000 : ℝ))
      (E := (cell12448 ⟨18, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41726329556219 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (228373696589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_19 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (83418047634273 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283740961753 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨19, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (83418047634273 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283740961753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12449_0 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (84079864529047 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283531409837 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨0, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (84079864529047 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283531409837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_1 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (5252800496603 / 6250000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570883858311 / 25000000000000 : ℝ))
      (E := (cell12449 ⟨1, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (5252800496603 / 6250000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570883858311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_2 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (84009776412047 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141769702547 / 50000000000000 : ℝ))
      (E := (cell12449 ⟨2, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (84009776412047 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141769702547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_3 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41987384945743 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283543392541 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨3, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41987384945743 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283543392541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_4 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83939788347401 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283547404693 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨4, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83939788347401 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283547404693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_5 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41952415871711 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141775696249 / 50000000000000 : ℝ))
      (E := (cell12449 ⟨5, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41952415871711 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141775696249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_6 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83869900043371 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283555364477 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨6, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83869900043371 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283555364477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_7 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (4191749660563 / 5000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283559386841 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨7, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (4191749660563 / 5000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283559386841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_8 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (10475013901411 / 12500000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (22835634097 / 1000000000000 : ℝ))
      (E := (cell12449 ⟨8, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (10475013901411 / 12500000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (22835634097 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_9 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (20941313501961 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283567382813 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨9, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (20941313501961 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283567382813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_10 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (16746084313101 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570892842907 / 25000000000000 : ℝ))
      (E := (cell12449 ⟨10, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (16746084313101 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570892842907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_11 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (8369561384903 / 10000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456715076679 / 20000000000000 : ℝ))
      (E := (cell12449 ⟨11, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (8369561384903 / 10000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456715076679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_12 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (20915207705841 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283579367047 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨12, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (20915207705841 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283579367047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_13 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (20906518113409 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (285447923419 / 12500000000000 : ℝ))
      (E := (cell12449 ⟨13, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (20906518113409 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (285447923419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_14 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41795669352577 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141793667293 / 50000000000000 : ℝ))
      (E := (cell12449 ⟨14, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41795669352577 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141793667293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_15 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (8355662954341 / 10000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283591331131 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨15, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (8355662954341 / 10000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283591331131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_16 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83521944934073 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570898845749 / 25000000000000 : ℝ))
      (E := (cell12449 ⟨16, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83521944934073 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570898845749 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_17 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83487284842991 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (91343975183 / 4000000000000 : ℝ))
      (E := (cell12449 ⟨17, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83487284842991 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (91343975183 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_18 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83452649236191 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456720665249 / 20000000000000 : ℝ))
      (E := (cell12449 ⟨18, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83452649236191 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456720665249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_19 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (83418038079873 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283607344599 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨19, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (83418038079873 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283607344599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

end BstLean.Part268
