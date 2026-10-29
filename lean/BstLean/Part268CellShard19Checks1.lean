import BstLean.Part268CellShard19Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12825_20 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (41690049083269 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447292410161 / 20000000000000 : ℝ))
      (E := (cell12825 ⟨20, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (41690049083269 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447292410161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_21 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (104182067173 / 125000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118233017773 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨21, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (104182067173 / 125000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118233017773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_22 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20827808373963 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118235015689 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨22, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20827808373963 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118235015689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_23 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (2081920935153 / 2500000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (139779627617 / 6250000000000 : ℝ))
      (E := (cell12825 ⟨23, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (2081920935153 / 2500000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (139779627617 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_24 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20810616359149 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236478070371 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨24, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20810616359149 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236478070371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_25 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (41604058777421 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (8736258053 / 390625000000 : ℝ))
      (E := (cell12825 ⟨25, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (41604058777421 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (8736258053 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_26 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (10396724216073 / 12500000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279560759587 / 12500000000000 : ℝ))
      (E := (cell12825 ⟨26, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (10396724216073 / 12500000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279560759587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_27 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20784873481429 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447298011987 / 20000000000000 : ℝ))
      (E := (cell12825 ⟨27, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20784873481429 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447298011987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_28 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83105218114293 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236494072101 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨28, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83105218114293 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236494072101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_29 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (10383870782817 / 12500000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447299611373 / 20000000000000 : ℝ))
      (E := (cell12825 ⟨29, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (10383870782817 / 12500000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447299611373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_30 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (3321469533553 / 4000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236502074629 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨30, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (3321469533553 / 4000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236502074629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_31 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (16600506862341 / 20000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118253034279 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨31, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (16600506862341 / 20000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118253034279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_32 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (41484177074939 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236510098643 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨32, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (41484177074939 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236510098643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_33 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82934197822207 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236514107549 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨33, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82934197822207 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236514107549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_34 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82900065297713 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236518096239 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨34, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82900065297713 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236518096239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_35 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82865956545573 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (34945658189 / 1562500000000 : ℝ))
      (E := (cell12825 ⟨35, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82865956545573 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (34945658189 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_36 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (41415935767561 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118263037187 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨36, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (41415935767561 / 50000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118263037187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_37 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (1655956204717 / 2000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236530123359 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨37, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (1655956204717 / 2000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236530123359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_38 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82763772617401 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559133523781 / 25000000000000 : ℝ))
      (E := (cell12825 ⟨38, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82763772617401 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559133523781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_39 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (82729758649573 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559134526729 / 25000000000000 : ℝ))
      (E := (cell12825 ⟨39, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (82729758649573 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559134526729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12826_20 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83380089553577 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236343261587 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨20, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83380089553577 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236343261587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_21 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (5209102839497 / 6250000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559086808359 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨21, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (5209102839497 / 6250000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559086808359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_22 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (8331122549549 / 10000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (279543909427 / 12500000000000 : ℝ))
      (E := (cell12826 ⟨22, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (8331122549549 / 10000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (279543909427 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_23 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83276829711417 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236355274447 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨23, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83276829711417 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236355274447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_24 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (10405307255891 / 12500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236359292181 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨24, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (10405307255891 / 12500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236359292181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_25 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (10401013808773 / 12500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447272654663 / 20000000000000 : ℝ))
      (E := (cell12826 ⟨25, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (10401013808773 / 12500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447272654663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_26 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83173786948313 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236367279077 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨26, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83173786948313 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236367279077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_27 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (1299054491397 / 1562500000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236371253651 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨27, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (1299054491397 / 1562500000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236371253651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_28 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83105211941527 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (279546907231 / 12500000000000 : ℝ))
      (E := (cell12826 ⟨28, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83105211941527 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (279546907231 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_29 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (8307096039289 / 10000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118189646921 / 50000000000000 : ℝ))
      (E := (cell12826 ⟨29, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (8307096039289 / 10000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118189646921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_30 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (2075918319297 / 2500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559095826263 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨30, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (2075918319297 / 2500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559095826263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_31 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83002529047041 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236387293123 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨31, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83002529047041 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236387293123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_32 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (20742087296769 / 25000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559097829511 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨32, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (20742087296769 / 25000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559097829511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_33 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82934193160849 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (27954941531 / 1250000000000 : ℝ))
      (E := (cell12826 ⟨33, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82934193160849 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (27954941531 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_34 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41450030468691 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236399307393 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨34, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41450030468691 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236399307393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_35 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (82865952485853 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447280666433 / 20000000000000 : ℝ))
      (E := (cell12826 ⟨35, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (82865952485853 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447280666433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_36 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41415933887799 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236407338713 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨36, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41415933887799 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236407338713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_37 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41398903388053 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223641132733 / 10000000000000 : ℝ))
      (E := (cell12826 ⟨37, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41398903388053 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (223641132733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_38 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (646591948883 / 781250000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118207678397 / 50000000000000 : ℝ))
      (E := (cell12826 ⟨38, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (646591948883 / 781250000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118207678397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_39 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (1654595115763 / 2000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447283873657 / 20000000000000 : ℝ))
      (E := (cell12826 ⟨39, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (1654595115763 / 2000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447283873657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12827_20 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83380080942183 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236224526853 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨20, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83380080942183 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236224526853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_21 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41672818563517 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (139764280367 / 6250000000000 : ℝ))
      (E := (cell12827 ⟨21, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41672818563517 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (139764280367 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_22 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83311217496621 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236232515723 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨22, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83311217496621 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236232515723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_23 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83276822018171 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (69882390729 / 3125000000000 : ℝ))
      (E := (cell12827 ⟨23, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83276822018171 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (69882390729 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_24 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (2081061266477 / 2500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (17470628987 / 781250000000 : ℝ))
      (E := (cell12827 ⟨24, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (2081061266477 / 2500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (17470628987 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_25 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83208103386909 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236244539851 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨25, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83208103386909 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236244539851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_26 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (20793445042347 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (223624853631 / 10000000000000 : ℝ))
      (E := (cell12827 ⟨26, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (20793445042347 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (223624853631 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_27 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83139480974411 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236252560731 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨27, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83139480974411 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236252560731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_28 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (16621041154007 / 20000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559064139261 / 25000000000000 : ℝ))
      (E := (cell12827 ⟨28, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (16621041154007 / 20000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559064139261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_29 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41535477262241 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559065131837 / 25000000000000 : ℝ))
      (E := (cell12827 ⟨29, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41535477262241 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559065131837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_30 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (10379590900767 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118132266021 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨30, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (10379590900767 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118132266021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_31 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83002523783541 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118134286421 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨31, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83002523783541 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118134286421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_32 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82968344225403 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236272534087 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨32, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82968344225403 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236272534087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_33 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (10366773562573 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (223627653409 / 10000000000000 : ℝ))
      (E := (cell12827 ⟨33, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (10366773562573 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (223627653409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_34 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (20725014144527 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118140286941 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨34, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (20725014144527 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118140286941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_35 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41432974213577 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236284595629 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨35, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41432974213577 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236284595629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_36 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41415932008529 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559072149961 / 25000000000000 : ℝ))
      (E := (cell12827 ⟨36, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41415932008529 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (559072149961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_37 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82797803317311 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236292586817 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨37, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82797803317311 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236292586817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_38 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (82763766297559 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (69884269229 / 3125000000000 : ℝ))
      (E := (cell12827 ⟨38, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (82763766297559 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (69884269229 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_39 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41364876463801 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (111815028391 / 5000000000000 : ℝ))
      (E := (cell12827 ⟨39, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41364876463801 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (111815028391 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12828_20 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (20845018083089 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236105788313 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨20, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (20845018083089 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236105788313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_21 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41672814411823 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236109792853 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨21, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41672814411823 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236109792853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_22 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (16662241899849 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118056905319 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨22, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (16662241899849 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118056905319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_23 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41638407163191 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559029446719 / 25000000000000 : ℝ))
      (E := (cell12828 ⟨23, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41638407163191 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559029446719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_24 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (20810610818113 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (111806089161 / 5000000000000 : ℝ))
      (E := (cell12828 ⟨24, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (20810610818113 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (111806089161 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_25 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41604048152509 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236125802769 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨25, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41604048152509 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236125802769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_26 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (8317377339181 / 10000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118064894981 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨26, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (8317377339181 / 10000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118064894981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_27 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83139474500723 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (279516725727 / 12500000000000 : ℝ))
      (E := (cell12828 ⟨27, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83139474500723 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (279516725727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_28 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (10388149949977 / 12500000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236137794257 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨28, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (10388149949977 / 12500000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236137794257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_29 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (2595967145541 / 3125000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (139758863493 / 6250000000000 : ℝ))
      (E := (cell12828 ⟨29, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (2595967145541 / 3125000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (139758863493 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_30 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83036721641593 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (139759113383 / 6250000000000 : ℝ))
      (E := (cell12828 ⟨30, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83036721641593 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (139759113383 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_31 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83002518521207 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118074924583 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨31, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83002518521207 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118074924583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_32 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82968339264857 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236153863919 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨32, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82968339264857 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236153863919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_33 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82934183841411 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559039464893 / 25000000000000 : ℝ))
      (E := (cell12828 ⟨33, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82934183841411 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559039464893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_34 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82900052219889 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236161837089 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨34, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82900052219889 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236161837089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_35 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41432972184737 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (279520731981 / 12500000000000 : ℝ))
      (E := (cell12828 ⟨35, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41432972184737 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (279520731981 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_36 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82831860259501 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236169857767 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨36, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82831860259501 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236169857767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_37 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82797799859463 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118086921567 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨37, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82797799859463 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118086921567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_38 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82763763139007 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236177870727 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨38, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82763763139007 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236177870727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_39 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (82729750067931 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (17470170951 / 781250000000 : ℝ))
      (E := (cell12828 ⟨39, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (82729750067931 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (17470170951 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12829_20 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (16676012744819 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235987104259 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨20, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (16676012744819 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235987104259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_21 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (20836405130447 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (558997774017 / 25000000000000 : ℝ))
      (E := (cell12829 ⟨21, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (20836405130447 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (558997774017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_22 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83311201503363 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235995101823 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨22, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83311201503363 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235995101823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_23 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83276806636049 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447199825019 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨23, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83276806636049 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447199825019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_24 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83242435887243 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118001555417 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨24, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83242435887243 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118001555417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_25 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83208089224509 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (13975044503 / 625000000000 : ℝ))
      (E := (cell12829 ⟨25, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83208089224509 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (13975044503 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_26 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41586883307789 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118005549233 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨26, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41586883307789 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118005549233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_27 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41569734014173 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (559003776453 / 25000000000000 : ℝ))
      (E := (cell12829 ⟨27, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41569734014173 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (559003776453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_28 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83105193430871 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118009572461 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨28, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83105193430871 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118009572461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_29 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41535471395689 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236023100961 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨29, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41535471395689 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236023100961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_30 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83036716078251 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236027151307 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨30, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83036716078251 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236027151307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_31 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (20750628315009 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118015561049 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨31, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (20750628315009 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118015561049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_32 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (518552089409 / 625000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118017565911 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨32, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (518552089409 / 625000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1118017565911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_33 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82934179183329 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (111801956157 / 5000000000000 : ℝ))
      (E := (cell12829 ⟨33, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82934179183329 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (111801956157 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_34 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82900047862727 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236043155633 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨34, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82900047862727 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236043155633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_35 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41432970156407 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447209434293 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨35, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41432970156407 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447209434293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_36 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82831856502929 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236051171147 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨36, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82831856502929 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236051171147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_37 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (82797796402563 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (279506894371 / 12500000000000 : ℝ))
      (E := (cell12829 ⟨37, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (82797796402563 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (279506894371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_38 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41381879990683 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447211836341 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨38, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41381879990683 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447211836341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_39 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (5170609200571 / 6250000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236063192539 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨39, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (5170609200571 / 6250000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2236063192539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12830_20 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83380055117401 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (5589671041 / 250000000000 : ℝ))
      (E := (cell12830 ⟨20, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83380055117401 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (5589671041 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_21 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83345612221459 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (223587245383 / 10000000000000 : ℝ))
      (E := (cell12830 ⟨21, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83345612221459 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (223587245383 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_22 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (20827798377243 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117938223809 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨22, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (20827798377243 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117938223809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_23 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83276798947171 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117940229811 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨23, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83276798947171 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117940229811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_24 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83242428503453 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (447176886959 / 20000000000000 : ℝ))
      (E := (cell12830 ⟨24, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83242428503453 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (447176886959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_25 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83208082145383 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235888434573 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨25, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83208082145383 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235888434573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_26 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (20793439960173 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235892461823 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨26, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (20793439960173 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235892461823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_27 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41569730778639 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117948230361 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨27, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41569730778639 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117948230361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_28 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83105187263199 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558975108401 / 25000000000000 : ℝ))
      (E := (cell12830 ⟨28, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83105187263199 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558975108401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_29 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83070936926681 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235904441069 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨29, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83070936926681 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235904441069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_30 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (20759177629027 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235908485059 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨30, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (20759177629027 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235908485059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_31 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83002508000029 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235912450187 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨31, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83002508000029 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235912450187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_32 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (82968329347151 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117958227471 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨32, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (82968329347151 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117958227471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_33 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (4146708726317 / 5000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (111796025029 / 5000000000000 : ℝ))
      (E := (cell12830 ⟨33, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (4146708726317 / 5000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (111796025029 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_34 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (4145002175331 / 5000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (447184894179 / 20000000000000 : ℝ))
      (E := (cell12830 ⟨34, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (4145002175331 / 5000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (447184894179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_35 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41432968128587 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558982120959 / 25000000000000 : ℝ))
      (E := (cell12830 ⟨35, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41432968128587 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558982120959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_36 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (82831852747339 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (55898312033 / 2500000000000 : ℝ))
      (E := (cell12830 ⟨36, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (82831852747339 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (55898312033 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_37 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (82797792946611 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235936522321 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨37, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (82797792946611 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235936522321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_38 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (20690939206159 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (44718809791 / 2000000000000 : ℝ))
      (E := (cell12830 ⟨38, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (20690939206159 / 25000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (44718809791 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_39 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (82729744351217 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558986125063 / 25000000000000 : ℝ))
      (E := (cell12830 ⟨39, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (82729744351217 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558986125063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12831_20 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (5211252907017 / 6250000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (223574978303 / 10000000000000 : ℝ))
      (E := (cell12831 ⟨20, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (5211252907017 / 6250000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (223574978303 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_21 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41672801961329 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558938451957 / 25000000000000 : ℝ))
      (E := (cell12831 ⟨21, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41672801961329 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558938451957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_22 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41655592758037 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558939447421 / 25000000000000 : ℝ))
      (E := (cell12831 ⟨22, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41655592758037 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (558939447421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_23 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83276791259749 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235761790459 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨23, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83276791259749 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235761790459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_24 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41621210560541 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (139735363343 / 6250000000000 : ℝ))
      (E := (cell12831 ⟨24, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41621210560541 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (139735363343 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_25 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83208075067639 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (111788490173 / 5000000000000 : ℝ))
      (E := (cell12831 ⟨25, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83208075067639 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (111788490173 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_26 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (5198359566697 / 6250000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235773821603 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨26, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (5198359566697 / 6250000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235773821603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_27 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41569727543759 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117888906047 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨27, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41569727543759 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117888906047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_28 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83105181096799 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235781835741 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨28, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83105181096799 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235781835741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_29 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (4153546553161 / 5000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235785836213 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨29, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (4153546553161 / 5000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235785836213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_30 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41518352477583 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235789815381 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨30, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41518352477583 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235789815381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_31 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83002502741187 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279474229179 / 12500000000000 : ℝ))
      (E := (cell12831 ⟨31, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83002502741187 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279474229179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_32 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82968324389989 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (6986868229 / 312500000000 : ℝ))
      (E := (cell12831 ⟨32, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82968324389989 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (6986868229 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_33 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82934169870441 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (139737617169 / 6250000000000 : ℝ))
      (E := (cell12831 ⟨33, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82934169870441 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (139737617169 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_34 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (5181252446973 / 6250000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235805841497 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨34, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (5181252446973 / 6250000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235805841497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_35 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (10358241525319 / 12500000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235809851609 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨35, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (10358241525319 / 12500000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235809851609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_36 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82831848992733 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279476730869 / 12500000000000 : ℝ))
      (E := (cell12831 ⟨36, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82831848992733 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279476730869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_37 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41398894745803 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279477235813 / 12500000000000 : ℝ))
      (E := (cell12831 ⟨37, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41398894745803 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279477235813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_38 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41381876834409 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117910926487 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨38, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41381876834409 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117910926487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_39 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (82729741494173 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117912931803 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨39, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (82729741494173 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117912931803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12832_20 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20845009477177 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235631204149 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨20, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20845009477177 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235631204149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_21 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83345595625387 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (17885081731 / 800000000000 : ℝ))
      (E := (cell12832 ⟨21, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83345595625387 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (17885081731 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_22 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20827794381167 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235639186361 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨22, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20827794381167 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235639186361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_23 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41638391786891 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (69863849249 / 3125000000000 : ℝ))
      (E := (cell12832 ⟨23, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41638391786891 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (69863849249 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_24 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (8324241374013 / 10000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (139727949283 / 6250000000000 : ℝ))
      (E := (cell12832 ⟨24, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (8324241374013 / 10000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (139727949283 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_25 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83208067991277 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235651227141 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨25, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83208067991277 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235651227141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_26 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83173746294957 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235655236237 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨26, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83173746294957 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235655236237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_27 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20784862154767 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235659218379 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨27, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20784862154767 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235659218379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_28 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (10388146866459 / 12500000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (143082447 / 6400000000 : ℝ))
      (E := (cell12832 ⟨28, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (10388146866459 / 12500000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (143082447 / 6400000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_29 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (16614185040199 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235667227893 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨29, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (16614185040199 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235667227893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_30 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83036699395423 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235671259327 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨30, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83036699395423 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235671259327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_31 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83002497483507 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (279459401661 / 12500000000000 : ℝ))
      (E := (cell12832 ⟨31, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83002497483507 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (279459401661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_32 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41484159716977 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235679266837 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨32, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41484159716977 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235679266837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_33 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82934165215633 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (279460405689 / 12500000000000 : ℝ))
      (E := (cell12832 ⟨33, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82934165215633 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (279460405689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_34 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82900034797571 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117843633719 / 50000000000000 : ℝ))
      (E := (cell12832 ⟨34, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82900034797571 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117843633719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_35 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (1657318562979 / 2000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (111784563739 / 5000000000000 : ℝ))
      (E := (cell12832 ⟨35, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (1657318562979 / 2000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (111784563739 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_36 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (8283184523911 / 10000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447139053609 / 20000000000000 : ℝ))
      (E := (cell12832 ⟨36, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (8283184523911 / 10000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447139053609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_37 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82797786037547 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235699247519 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨37, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82797786037547 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235699247519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_38 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (82763750513911 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235703271979 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨38, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (82763750513911 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235703271979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_39 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20682434659501 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (11178536413 / 500000000000 : ℝ))
      (E := (cell12832 ⟨39, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20682434659501 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (11178536413 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12833_20 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (8338002930671 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558878155367 / 25000000000000 : ℝ))
      (E := (cell12833 ⟨20, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (8338002930671 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558878155367 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_21 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83345587329643 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (55887915529 / 2500000000000 : ℝ))
      (E := (cell12833 ⟨21, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83345587329643 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (55887915529 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_22 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83311169534753 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558880159413 / 25000000000000 : ℝ))
      (E := (cell12833 ⟨22, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83311169534753 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558880159413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_23 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (8327677588927 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235524616151 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨23, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (8327677588927 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235524616151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_24 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (16648481272119 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447105723661 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨24, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (16648481272119 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447105723661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_25 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (10401007614537 / 12500000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (223553264721 / 10000000000000 : ℝ))
      (E := (cell12833 ⟨25, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (10401007614537 / 12500000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (223553264721 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_26 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83173739524107 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235536647297 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨26, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83173739524107 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235536647297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_27 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41569721075963 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (279442577641 / 12500000000000 : ℝ))
      (E := (cell12833 ⟨27, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41569721075963 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (279442577641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_28 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83105168767817 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (223554462951 / 10000000000000 : ℝ))
      (E := (cell12833 ⟨28, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83105168767817 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (223554462951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_29 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (16614183868001 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558887168653 / 25000000000000 : ℝ))
      (E := (cell12833 ⟨29, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (16614183868001 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558887168653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_30 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (1037958672961 / 1250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235552641321 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨30, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (1037958672961 / 1250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235552641321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_31 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83002492226991 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235556648303 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨31, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83002492226991 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235556648303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_32 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41484157239523 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235560638471 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨32, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41484157239523 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235560638471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_33 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82934160561917 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (5588911679 / 250000000000 : ℝ))
      (E := (cell12833 ⟨33, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82934160561917 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (5588911679 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_34 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (20725007611157 / 25000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235568690103 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨34, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (20725007611157 / 25000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235568690103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_35 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41432962048183 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235572694711 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨35, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41432962048183 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235572694711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_36 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (82831841486469 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447115337187 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨36, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (82831841486469 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447115337187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_37 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (16559556516887 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235580664057 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨37, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (16559556516887 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235580664057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_38 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41381873679957 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447116937571 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨38, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41381873679957 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447116937571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_39 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (8272973578271 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117794349251 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨39, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (8272973578271 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117794349251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12834_20 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (3335200828251 / 4000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235394034987 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨20, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (3335200828251 / 4000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235394034987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_21 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83345579035427 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235398080497 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨21, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83345579035427 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235398080497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_22 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (10413895193291 / 12500000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235402085219 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨22, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (10413895193291 / 12500000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235402085219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_23 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (20819192051553 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235406052647 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨23, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (20819192051553 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235406052647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_24 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41621199491239 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235410102817 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨24, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41621199491239 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235410102817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_25 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83208053842697 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (447082812733 / 20000000000000 : ℝ))
      (E := (cell12834 ⟨25, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83208053842697 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (447082812733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_26 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41586866377301 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235418113213 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨26, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41586866377301 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235418113213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_27 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (20784858921523 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117711039397 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨27, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (20784858921523 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117711039397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_28 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83105162605233 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235426079623 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨28, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83105162605233 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235426079623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_29 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83070913480251 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (558857529467 / 25000000000000 : ℝ))
      (E := (cell12834 ⟨29, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83070913480251 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (558857529467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_30 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (5189793017471 / 6250000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117717039207 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨30, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (5189793017471 / 6250000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117717039207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_31 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83002486971637 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (27942976731 / 1250000000000 : ℝ))
      (E := (cell12834 ⟨31, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83002486971637 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (27942976731 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_32 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (16593661905053 / 20000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235442123897 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨32, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (16593661905053 / 20000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235442123897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_33 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (8293415590929 / 10000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117723047187 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨33, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (8293415590929 / 10000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117723047187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_34 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (4145001304637 / 5000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235450109489 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨34, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (4145001304637 / 5000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235450109489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_35 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (12947800007 / 15625000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117727055701 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨35, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (12947800007 / 15625000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117727055701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_36 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (82831837734811 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117729079643 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨36, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (82831837734811 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117729079643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_37 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (8279777913227 / 10000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235462136117 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨37, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (8279777913227 / 10000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235462136117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_38 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (20690936051707 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235466159313 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨38, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (20690936051707 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235466159313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_39 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (8272973292829 / 10000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235470170047 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨39, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (8272973292829 / 10000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235470170047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12835_20 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (16676002421481 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235275561289 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨20, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (16676002421481 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235275561289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_21 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83345570742739 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (279409942009 / 12500000000000 : ℝ))
      (E := (cell12835 ⟨21, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83345570742739 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (279409942009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_22 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (16662230711879 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (111764176453 / 5000000000000 : ℝ))
      (E := (cell12835 ⟨22, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (16662230711879 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (111764176453 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_23 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (1301199383197 / 1562500000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235287543819 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨23, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (1301199383197 / 1562500000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235287543819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_24 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83242391605779 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235291583679 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨24, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83242391605779 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235291583679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_25 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41604023385239 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235295534919 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨25, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41604023385239 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235295534919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_26 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (2079343149661 / 2500000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558824893889 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨26, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (2079343149661 / 2500000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558824893889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_27 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41569714610783 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235303591379 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨27, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41569714610783 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235303591379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_28 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83105156443921 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (447061516943 / 20000000000000 : ℝ))
      (E := (cell12835 ⟨28, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83105156443921 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (447061516943 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_29 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (20767726905433 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117655778831 / 50000000000000 : ℝ))
      (E := (cell12835 ⟨29, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (20767726905433 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117655778831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_30 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (8303668272339 / 10000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (223531557061 / 10000000000000 : ℝ))
      (E := (cell12835 ⟨30, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (8303668272339 / 10000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (223531557061 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_31 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41501240858723 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235319566719 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨31, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41501240858723 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235319566719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_32 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (8296830457261 / 10000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235323605973 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨32, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (8296830457261 / 10000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235323605973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_33 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41467075628877 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235327631027 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨33, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41467075628877 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235327631027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_34 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41450010870953 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235331584219 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨34, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41450010870953 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235331584219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_35 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (20716478998563 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235335642139 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨35, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (20716478998563 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235335642139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_36 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41415916992067 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (447067925887 / 20000000000000 : ℝ))
      (E := (cell12835 ⟨36, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41415916992067 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (447067925887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_37 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (1655955513621 / 2000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235343605011 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨37, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (1655955513621 / 2000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235343605011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_38 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (20690935263663 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117673813821 / 50000000000000 : ℝ))
      (E := (cell12835 ⟨38, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (20690935263663 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117673813821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_39 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (16545946014949 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235351638499 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨39, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (16545946014949 / 20000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235351638499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12836_20 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83380003510099 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117578512751 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨20, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83380003510099 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117578512751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_21 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83345562451577 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235161046203 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨21, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83345562451577 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235161046203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_22 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (1301736649593 / 1562500000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235165085857 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨22, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (1301736649593 / 1562500000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235165085857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_23 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83276752844457 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558792272417 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨23, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83276752844457 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558792272417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_24 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (2601324507203 / 3125000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (69849158153 / 3125000000000 : ℝ))
      (E := (cell12836 ⟨24, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (2601324507203 / 3125000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (69849158153 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_25 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83208039699639 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558794265243 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨25, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83208039699639 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558794265243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_26 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83173719219623 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235181092759 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨26, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83173719219623 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235181092759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_27 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (20784855689587 / 25000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235185100429 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨27, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (20784855689587 / 25000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235185100429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_28 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (2077628757097 / 2500000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (223518908631 / 10000000000000 : ℝ))
      (E := (cell12836 ⟨28, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (2077628757097 / 2500000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (223518908631 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_29 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (2595965680139 / 3125000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235193111 / 100000000000 : ℝ))
      (E := (cell12836 ⟨29, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (2595965680139 / 3125000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235193111 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_30 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83036677168443 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235197117907 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨30, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83036677168443 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235197117907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_31 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (2593827389513 / 3125000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (34925017323 / 1562500000000 : ℝ))
      (E := (cell12836 ⟨31, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (2593827389513 / 3125000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (34925017323 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_32 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82968299621081 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (22352050847 / 1000000000000 : ℝ))
      (E := (cell12836 ⟨32, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82968299621081 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (22352050847 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_33 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82934146607307 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558802276443 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨33, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82934146607307 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558802276443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_34 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (663200139137 / 800000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235213114293 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨34, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (663200139137 / 800000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235213114293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_35 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41432955972361 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117608555497 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨35, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41432955972361 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117608555497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_36 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82831830234439 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (44704423101 / 2000000000000 : ℝ))
      (E := (cell12836 ⟨36, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82831830234439 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (44704423101 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_37 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (82797772230777 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (223522512943 / 10000000000000 : ℝ))
      (E := (cell12836 ⟨37, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (82797772230777 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (223522512943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_38 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41381868951693 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558807287889 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨38, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41381868951693 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558807287889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_39 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41364863611037 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235233162597 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨39, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41364863611037 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235233162597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12837_20 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (20844998728589 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (894015441 / 40000000000 : ℝ))
      (E := (cell12837 ⟨20, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (20844998728589 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (894015441 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_21 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41672777080971 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235042610889 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨21, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41672777080971 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235042610889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_22 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41655568794999 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235046580593 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨22, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41655568794999 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235046580593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_23 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (260239828643 / 312500000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (223505057347 / 10000000000000 : ℝ))
      (E := (cell12837 ⟨23, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (260239828643 / 312500000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (223505057347 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_24 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (8324237685663 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235054592849 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨24, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (8324237685663 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235054592849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_25 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83208032630181 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117529291707 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨25, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83208032630181 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117529291707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_26 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83173712454149 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235062606389 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨26, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83173712454149 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235062606389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_27 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (20784854074109 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (447013321189 / 20000000000000 : ℝ))
      (E := (cell12837 ⟨27, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (20784854074109 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (447013321189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_28 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83105144125109 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235070642887 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨28, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83105144125109 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235070642887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_29 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41535447954199 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (17880596819 / 800000000000 : ℝ))
      (E := (cell12837 ⟨29, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41535447954199 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (17880596819 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_30 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83036671614693 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (279384825407 / 12500000000000 : ℝ))
      (E := (cell12837 ⟨30, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83036671614693 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (279384825407 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_31 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83002471212549 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235082647237 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨31, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83002471212549 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235082647237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_32 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82968294670677 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (44701732373 / 2000000000000 : ℝ))
      (E := (cell12837 ⟨32, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82968294670677 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (44701732373 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_33 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (1658682839159 / 2000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (11175453179 / 500000000000 : ℝ))
      (E := (cell12837 ⟨33, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (1658682839159 / 2000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (11175453179 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_34 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41450006521699 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (558773660273 / 25000000000000 : ℝ))
      (E := (cell12837 ⟨34, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41450006521699 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (558773660273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_35 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82865907896209 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117549317627 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨35, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82865907896209 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117549317627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_36 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41415913242863 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117551338731 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨36, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41415913242863 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117551338731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_37 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (10349721097681 / 12500000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117553325343 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨37, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (10349721097681 / 12500000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117553325343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_38 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (8276373475303 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117555336171 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨38, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (8276373475303 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117555336171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_39 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (82729724370277 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235114683603 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨39, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (82729724370277 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235114683603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12838_20 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (5211249145011 / 6250000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234920175703 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨20, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (5211249145011 / 6250000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234920175703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_21 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83345545873833 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234924171817 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨21, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83345545873833 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234924171817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_22 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41655564803767 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117464094143 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨22, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41655564803767 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117464094143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_23 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (16655347497703 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117466085157 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨23, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (16655347497703 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117466085157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_24 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (4162118474209 / 5000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234936179543 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨24, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (4162118474209 / 5000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234936179543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_25 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41604012781051 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117470080329 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨25, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41604012781051 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117470080329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_26 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41586852845009 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234944174881 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨26, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41586852845009 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234944174881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_27 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83139409835831 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234948166383 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨27, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83139409835831 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234948166383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_28 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83105137967609 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234952195967 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨28, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83105137967609 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234952195967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_29 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41535445026791 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (34921190739 / 1562500000000 : ℝ))
      (E := (cell12838 ⟨29, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41535445026791 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (34921190739 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_30 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41518333031071 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446992040447 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨30, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41518333031071 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446992040447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_31 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83002465961843 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117482091209 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨31, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83002465961843 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117482091209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_32 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (82968289721399 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117484103913 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨32, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (82968289721399 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117484103913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_33 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41467068654841 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446994444223 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨33, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41467068654841 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446994444223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_34 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (20725002173931 / 25000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234976223237 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨34, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (20725002173931 / 25000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234976223237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_35 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (82865903848713 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117490107461 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨35, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (82865903848713 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117490107461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_36 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41415911368997 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234984255341 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨36, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41415911368997 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234984255341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_37 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (16559553066613 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (558747056867 / 25000000000000 : ℝ))
      (E := (cell12838 ⟨37, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (16559553066613 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (558747056867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_38 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (82763731603583 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446998449743 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨38, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (82763731603583 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446998449743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_39 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (82729721519353 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234996260257 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨39, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (82729721519353 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234996260257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12839_20 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41689988863779 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279350218139 / 12500000000000 : ℝ))
      (E := (cell12839 ⟨20, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41689988863779 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279350218139 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_21 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (333382150349 / 400000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234805728987 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨21, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (333382150349 / 400000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234805728987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_22 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83311121626559 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234809733921 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨22, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83311121626559 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234809733921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_23 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83276729812723 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (89392550539 / 4000000000000 : ℝ))
      (E := (cell12839 ⟨23, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83276729812723 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (89392550539 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_24 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41621181056573 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234817762593 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨24, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41621181056573 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234817762593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_25 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41604009247701 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (34919090511 / 1562500000000 : ℝ))
      (E := (cell12839 ⟨25, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41604009247701 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (34919090511 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_26 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (8317369892723 / 10000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446965159647 / 20000000000000 : ℝ))
      (E := (cell12839 ⟨26, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (8317369892723 / 10000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446965159647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_27 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (20784850844133 / 25000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (139676861359 / 6250000000000 : ℝ))
      (E := (cell12839 ⟨27, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (20784850844133 / 25000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (139676861359 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_28 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41552565905689 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (8729819547 / 390625000000 : ℝ))
      (E := (cell12839 ⟨28, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41552565905689 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (8729819547 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_29 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83070884199999 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (55870945219 / 2500000000000 : ℝ))
      (E := (cell12839 ⟨29, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83070884199999 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (55870945219 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_30 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83036660510787 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117420898897 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨30, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83036660510787 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117420898897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_31 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41501230356149 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446969154553 / 20000000000000 : ℝ))
      (E := (cell12839 ⟨31, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41501230356149 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446969154553 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_32 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41484142386623 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446969958731 / 20000000000000 : ℝ))
      (E := (cell12839 ⟨32, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41484142386623 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446969958731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_33 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82934132662503 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234853803119 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨33, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82934132662503 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234853803119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_34 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82900004349103 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234857802109 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨34, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82900004349103 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234857802109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_35 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (16573179960447 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279357723919 / 12500000000000 : ℝ))
      (E := (cell12839 ⟨35, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (16573179960447 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279357723919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_36 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41415909495621 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117432915011 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨36, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41415909495621 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117432915011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_37 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (20699440471407 / 25000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117434900543 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨37, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (20699440471407 / 25000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117434900543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_38 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (16552745691009 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234873821963 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨38, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (16552745691009 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234873821963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_39 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (82729718669303 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117438916911 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨39, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (82729718669303 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117438916911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12840_20 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (83379969136503 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234683369017 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨20, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (83379969136503 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234683369017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_21 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (5209095581387 / 6250000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (279335924879 / 12500000000000 : ℝ))
      (E := (cell12840 ⟨21, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (5209095581387 / 6250000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (279335924879 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_22 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (83311113647073 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234691392513 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨22, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (83311113647073 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234691392513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_23 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41638361069191 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446939070591 / 20000000000000 : ℝ))
      (E := (cell12840 ⟨23, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41638361069191 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446939070591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_24 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (83242354743527 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (34917178131 / 1562500000000 : ℝ))
      (E := (cell12840 ⟨24, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (83242354743527 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (34917178131 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_25 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (83208011430081 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117351681367 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨25, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (83208011430081 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117351681367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_26 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (10396711520723 / 12500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234707418021 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨26, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (10396711520723 / 12500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234707418021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_27 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (4156969845927 / 5000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234711393573 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨27, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (4156969845927 / 5000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234711393573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_28 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41552562828209 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234715408601 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨28, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41552562828209 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234715408601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_29 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (1661417566953 / 2000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117359703383 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨29, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (1661417566953 / 2000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117359703383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_30 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (8303665496063 / 10000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234723389931 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨30, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (8303665496063 / 10000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234723389931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_31 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41501227731957 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117363709139 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨31, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41501227731957 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117363709139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_32 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (82968279826217 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (279341429339 / 12500000000000 : ℝ))
      (E := (cell12840 ⟨32, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (82968279826217 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (279341429339 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_33 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (82934128016413 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234735440411 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨33, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (82934128016413 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234735440411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_34 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (16580000000707 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (279342429541 / 12500000000000 : ℝ))
      (E := (cell12840 ⟨34, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (16580000000707 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (279342429541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_35 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (20716473939193 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234743423191 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨35, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (20716473939193 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234743423191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_36 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (2588494226421 / 3125000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234747460169 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨36, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (2588494226421 / 3125000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234747460169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_37 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41398879219567 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446950286047 / 20000000000000 : ℝ))
      (E := (cell12840 ⟨37, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41398879219567 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446950286047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_38 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (10345465663427 / 12500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (5586888627 / 250000000000 : ℝ))
      (E := (cell12840 ⟨38, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (10345465663427 / 12500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (5586888627 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_39 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41364857910063 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446951892607 / 20000000000000 : ℝ))
      (E := (cell12840 ⟨39, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41364857910063 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446951892607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12841_20 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (83379960547009 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558641247283 / 25000000000000 : ℝ))
      (E := (cell12841 ⟨20, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (83379960547009 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558641247283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_21 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (4167276050933 / 5000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117284503503 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨21, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (4167276050933 / 5000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117284503503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_22 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (3332444226763 / 4000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (223457304739 / 10000000000000 : ℝ))
      (E := (cell12841 ⟨22, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (3332444226763 / 4000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (223457304739 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_23 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41638357232747 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (55864426387 / 2500000000000 : ℝ))
      (E := (cell12841 ⟨23, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41638357232747 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (55864426387 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_24 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (20810586843831 / 25000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234581034533 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨24, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (20810586843831 / 25000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234581034533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_25 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (83208004366139 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117292522989 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨25, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (83208004366139 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117292522989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_26 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (1039671067571 / 1250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1745772683 / 78125000000 : ℝ))
      (E := (cell12841 ⟨26, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (1039671067571 / 1250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1745772683 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_27 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (83139390461853 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279324132541 / 12500000000000 : ℝ))
      (E := (cell12841 ⟨27, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (83139390461853 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279324132541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_28 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41552559751363 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117298534079 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨28, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41552559751363 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117298534079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_29 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41535436248267 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (111730052991 / 5000000000000 : ℝ))
      (E := (cell12841 ⟨29, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41535436248267 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (111730052991 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_30 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (8303664941167 / 10000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279325629647 / 12500000000000 : ℝ))
      (E := (cell12841 ⟨30, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (8303664941167 / 10000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279325629647 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_31 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (83002450216691 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (223460906041 / 10000000000000 : ℝ))
      (E := (cell12841 ⟨31, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (83002450216691 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (223460906041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_32 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82968274880313 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279326634053 / 12500000000000 : ℝ))
      (E := (cell12841 ⟨32, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82968274880313 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279326634053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_33 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82934123371411 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446923414879 / 20000000000000 : ℝ))
      (E := (cell12841 ⟨33, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82934123371411 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446923414879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_34 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41449997829509 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117310533639 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨34, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41449997829509 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117310533639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_35 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41432945856163 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (55865627761 / 2500000000000 : ℝ))
      (E := (cell12841 ⟨35, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41432945856163 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (55865627761 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_36 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (82831811500681 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117314543561 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨36, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (82831811500681 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117314543561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_37 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41398877496793 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (69832284841 / 3125000000000 : ℝ))
      (E := (cell12841 ⟨37, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41398877496793 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (69832284841 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_38 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (10345465270087 / 12500000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234637135227 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨38, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (10345465270087 / 12500000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234637135227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_39 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41364856485911 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234641089161 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨39, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41364856485911 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234641089161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12842_20 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83379951959077 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558611680509 / 25000000000000 : ℝ))
      (E := (cell12842 ⟨20, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83379951959077 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558611680509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_21 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (20836378184163 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (139653170491 / 6250000000000 : ℝ))
      (E := (cell12842 ⟨21, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (20836378184163 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (139653170491 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_22 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (16662219538513 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234454698547 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨22, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (16662219538513 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234454698547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_23 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83276706794057 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117229347981 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨23, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83276706794057 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117229347981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_24 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (16648468001707 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (89378508937 / 4000000000000 : ℝ))
      (E := (cell12842 ⟨24, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (16648468001707 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (89378508937 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_25 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (3328319892143 / 4000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (139654170351 / 6250000000000 : ℝ))
      (E := (cell12842 ⟨25, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (3328319892143 / 4000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (139654170351 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_26 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83173678646919 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117235352661 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨26, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83173678646919 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117235352661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_27 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83139384006471 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234474723553 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨27, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83139384006471 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234474723553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_28 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (2597034792197 / 3125000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234478724221 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨28, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (2597034792197 / 3125000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234478724221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_29 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (1661417332933 / 2000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234482709417 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨29, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (1661417332933 / 2000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234482709417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_30 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41518321931953 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234486739529 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨30, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41518321931953 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234486739529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_31 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (20750611242657 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (223449075771 / 10000000000000 : ℝ))
      (E := (cell12842 ⟨31, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (20750611242657 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (223449075771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_32 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82968269935533 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558623691341 / 25000000000000 : ℝ))
      (E := (cell12842 ⟨32, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82968269935533 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558623691341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_33 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82934118727497 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558624690917 / 25000000000000 : ℝ))
      (E := (cell12842 ⟨33, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82934118727497 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558624690917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_34 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41449995657777 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (89380110143 / 4000000000000 : ℝ))
      (E := (cell12842 ⟨34, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41449995657777 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (89380110143 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_35 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (2589558989653 / 3125000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117253397227 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨35, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (2589558989653 / 3125000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117253397227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_36 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82831807756871 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117255384771 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨36, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82831807756871 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117255384771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_37 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (82797751548981 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (223451479643 / 10000000000000 : ℝ))
      (E := (cell12842 ⟨37, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (82797751548981 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (223451479643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_38 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (20690929753721 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (446903751563 / 20000000000000 : ℝ))
      (E := (cell12842 ⟨38, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (20690929753721 / 25000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (446903751563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_39 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (8272971012439 / 10000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117261385469 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨39, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (8272971012439 / 10000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117261385469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12843_20 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41689971686353 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117164196429 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨20, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41689971686353 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117164196429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_21 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (10418188057021 / 12500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117166193319 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨21, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (10418188057021 / 12500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117166193319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_22 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41655544858771 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (223433640433 / 10000000000000 : ℝ))
      (E := (cell12843 ⟨22, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41655544858771 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (223433640433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_23 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (8327669912407 / 10000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (223434039113 / 10000000000000 : ℝ))
      (E := (cell12843 ⟨23, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (8327669912407 / 10000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (223434039113 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_24 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (83242332643161 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558586102169 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨24, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (83242332643161 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558586102169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_25 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (83207990242389 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558587100413 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨25, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (83207990242389 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558587100413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_26 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41586835944749 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279294053909 / 12500000000000 : ℝ))
      (E := (cell12843 ⟨26, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41586835944749 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279294053909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_27 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (16627875510479 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446871288341 / 20000000000000 : ℝ))
      (E := (cell12843 ⟨27, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (16627875510479 / 20000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446871288341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_28 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (1662102143983 / 2000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234360435273 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨28, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (1662102143983 / 2000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234360435273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_29 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (83070860797999 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (139647775879 / 6250000000000 : ℝ))
      (E := (cell12843 ⟨29, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (83070860797999 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (139647775879 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_30 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41518319158669 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117184219233 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨30, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41518319158669 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117184219233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_31 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (3320097589029 / 4000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (223437245163 / 10000000000000 : ℝ))
      (E := (cell12843 ⟨31, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (3320097589029 / 4000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (223437245163 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_32 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (20742066247969 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117188227481 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨32, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (20742066247969 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117188227481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_33 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (8293411408467 / 10000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234380449637 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨33, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (8293411408467 / 10000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234380449637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_34 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41449993486571 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (89375379809 / 4000000000000 : ℝ))
      (E := (cell12843 ⟨34, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41449993486571 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (89375379809 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_35 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41432941813241 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234388475237 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨35, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41432941813241 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234388475237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_36 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (2070795100351 / 2500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558598126859 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨36, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (2070795100351 / 2500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558598126859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_37 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (2069943702633 / 2500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (223439647479 / 10000000000000 : ℝ))
      (E := (cell12843 ⟨37, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (2069943702633 / 2500000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (223439647479 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_38 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (4138185793499 / 5000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234400494711 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨38, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (4138185793499 / 5000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234400494711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_39 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (82729707277831 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117202254183 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨39, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (82729707277831 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117202254183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12844_20 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (16675986957579 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117105059091 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨20, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (16675986957579 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117105059091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_21 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (10418187022151 / 12500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234214158299 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨21, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (10418187022151 / 12500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234214158299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_22 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83311081744007 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (4363707353 / 195312500000 : ℝ))
      (E := (cell12844 ⟨22, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83311081744007 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (4363707353 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_23 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (16655338291107 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234222140981 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨23, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (16655338291107 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234222140981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_24 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (104052906599 / 125000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117113074337 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨24, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (104052906599 / 125000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117113074337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_25 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83207983182581 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234230132493 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨25, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83207983182581 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234230132493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_26 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83173665133419 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234234153657 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨26, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83173665133419 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234234153657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_27 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83139371099623 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223423815633 / 10000000000000 : ℝ))
      (E := (cell12844 ⟨27, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83139371099623 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223423815633 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_28 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (16621020209853 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234242142833 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨28, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (16621020209853 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234242142833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_29 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (4153542747529 / 5000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234246173759 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨29, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (4153542747529 / 5000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234246173759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_30 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (41518316385983 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (17455079629 / 781250000000 : ℝ))
      (E := (cell12844 ⟨30, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (41518316385983 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (17455079629 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_31 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83002434481981 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234254200721 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨31, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83002434481981 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234254200721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_32 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (1296379063271 / 1562500000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223425819979 / 10000000000000 : ℝ))
      (E := (cell12844 ⟨32, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (1296379063271 / 1562500000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223425819979 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_33 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82934109442931 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (139641386931 / 6250000000000 : ℝ))
      (E := (cell12844 ⟨33, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82934109442931 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (139641386931 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_34 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (4144999131589 / 5000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117133087493 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨34, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (4144999131589 / 5000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117133087493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_35 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82865879585083 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234270211431 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨35, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82865879585083 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234270211431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_36 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82831800272189 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117137121067 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨36, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82831800272189 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117137121067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_37 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (82797744662603 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234278208681 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨37, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (82797744662603 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234278208681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_38 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (2586366022687 / 3125000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558570557121 / 25000000000000 : ℝ))
      (E := (cell12844 ⟨38, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (2586366022687 / 3125000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558570557121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_39 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (5170606527009 / 6250000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223428624271 / 10000000000000 : ℝ))
      (E := (cell12844 ⟨39, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (5170606527009 / 6250000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223428624271 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12845_20 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (16675985240929 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234091898009 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨20, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (16675985240929 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234091898009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_21 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83345487899771 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234095926209 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨21, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83345487899771 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234095926209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_22 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83311073771959 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (558524980357 / 25000000000000 : ℝ))
      (E := (cell12845 ⟨22, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83311073771959 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (558524980357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_23 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83276683788449 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234103887157 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨23, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83276683788449 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234103887157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_24 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41621158958327 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234107943419 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨24, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41621158958327 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234107943419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_25 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83207976124149 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (34907998721 / 1562500000000 : ℝ))
      (E := (cell12845 ⟨25, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83207976124149 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (34907998721 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_26 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (2079341459467 / 2500000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (223411593091 / 10000000000000 : ℝ))
      (E := (cell12845 ⟨26, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (2079341459467 / 2500000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (223411593091 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_27 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (16627872929631 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (558529981471 / 25000000000000 : ℝ))
      (E := (cell12845 ⟨27, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (16627872929631 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (558529981471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_28 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83105094900647 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (279265488173 / 12500000000000 : ℝ))
      (E := (cell12845 ⟨28, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83105094900647 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (279265488173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_29 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83070849104393 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117063965001 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨29, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83070849104393 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117063965001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_30 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83036627227789 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234131943143 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨30, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83036627227789 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234131943143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_31 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83002429239397 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234135946433 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨31, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83002429239397 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234135946433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_32 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41484127553967 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234139941277 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨32, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41484127553967 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234139941277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_33 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (2073352620057 / 2500000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117071993723 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨33, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (2073352620057 / 2500000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117071993723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_34 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (8289997829147 / 10000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (27926849609 / 1250000000000 : ℝ))
      (E := (cell12845 ⟨34, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (8289997829147 / 10000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (27926849609 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_35 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (82865875544699 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446830388879 / 20000000000000 : ℝ))
      (E := (cell12845 ⟨35, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (82865875544699 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446830388879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_36 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41415898265659 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117077986819 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨36, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41415898265659 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117077986819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_37 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (8279774122083 / 10000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446831999621 / 20000000000000 : ℝ))
      (E := (cell12845 ⟨37, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (8279774122083 / 10000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446831999621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_38 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (5172731848931 / 6250000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234163959137 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨38, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (5172731848931 / 6250000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234163959137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_39 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (646325793651 / 781250000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (223416797397 / 10000000000000 : ℝ))
      (E := (cell12845 ⟨39, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (646325793651 / 781250000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (223416797397 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12846_20 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41689958811477 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233973674049 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨20, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41689958811477 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233973674049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_21 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41672739811929 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233977690367 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨21, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41672739811929 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233977690367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_22 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83311065801397 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233981674407 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨22, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83311065801397 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233981674407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_23 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41638338061407 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233985688019 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨23, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41638338061407 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233985688019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_24 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (130066110243 / 156250000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116994867263 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨24, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (130066110243 / 156250000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116994867263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_25 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (16641593813419 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (69812303131 / 3125000000000 : ℝ))
      (E := (cell12846 ⟨25, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (16641593813419 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (69812303131 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_26 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41586825812641 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (11169988523 / 500000000000 : ℝ))
      (E := (cell12846 ⟨26, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41586825812641 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (11169988523 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_27 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (10392419774749 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234001691911 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨27, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (10392419774749 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234001691911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_28 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41552544376649 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (89360228917 / 4000000000000 : ℝ))
      (E := (cell12846 ⟨28, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41552544376649 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (89360228917 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_29 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83070843259437 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234009741297 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨29, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83070843259437 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234009741297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_30 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (10379577710601 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (446802749777 / 20000000000000 : ℝ))
      (E := (cell12846 ⟨30, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (10379577710601 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (446802749777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_31 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83002423997971 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117008873659 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨31, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83002423997971 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117008873659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_32 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82968250167647 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234021737997 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨32, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82968250167647 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234021737997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_33 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (16586820032543 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234025722097 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨33, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (16586820032543 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234025722097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_34 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82899973952211 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234029759187 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨34, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82899973952211 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234029759187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_35 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82865871505331 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (558508433193 / 25000000000000 : ℝ))
      (E := (cell12846 ⟨35, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82865871505331 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (558508433193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_36 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (3313271711657 / 4000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (279254720077 / 12500000000000 : ℝ))
      (E := (cell12846 ⟨36, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (3313271711657 / 4000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (279254720077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_37 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (82797737779999 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117020892187 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨37, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (82797737779999 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1117020892187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_38 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41381853220357 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234045804099 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨38, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41381853220357 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2234045804099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_39 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (10341212342923 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (558512440221 / 25000000000000 : ℝ))
      (E := (cell12846 ⟨39, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (10341212342923 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (558512440221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12847_20 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83379909042823 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116927752297 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨20, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83379909042823 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116927752297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_21 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83345471349467 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233859509093 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨21, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83345471349467 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233859509093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_22 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83311057832321 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116931770177 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨22, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83311057832321 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116931770177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_23 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (20819167114657 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233867543571 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨23, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (20819167114657 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233867543571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_24 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (416211515979 / 500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558467880499 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨24, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (416211515979 / 500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558467880499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_25 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83207962011417 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558468884263 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨25, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83207962011417 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558468884263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_26 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (10396705609153 / 12500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233879533161 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨26, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (10396705609153 / 12500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233879533161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_27 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (20784837937283 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233883512871 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨27, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (20784837937283 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233883512871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_28 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (16621016521443 / 20000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (111694376849 / 5000000000000 : ℝ))
      (E := (cell12847 ⟨28, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (16621016521443 / 20000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (111694376849 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_29 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (2595963669241 / 3125000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116945774571 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨29, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (2595963669241 / 3125000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116945774571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_30 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83036616143021 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (139618471951 / 6250000000000 : ℝ))
      (E := (cell12847 ⟨30, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83036616143021 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (139618471951 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_31 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (16600483751541 / 20000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233899544827 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨31, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (16600483751541 / 20000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233899544827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_32 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82968245228483 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (34904743593 / 1562500000000 : ℝ))
      (E := (cell12847 ⟨32, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82968245228483 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (34904743593 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_33 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (20733523881059 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (27923844633 / 1250000000000 : ℝ))
      (E := (cell12847 ⟨33, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (20733523881059 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (27923844633 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_34 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (41449984807001 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233911546389 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨34, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (41449984807001 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233911546389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_35 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (2589558358343 / 3125000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116957788283 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨35, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (2589558358343 / 3125000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116957788283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_36 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (8283178905251 / 10000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233919603071 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨36, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (8283178905251 / 10000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233919603071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_37 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (82797734340111 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (17452527871 / 781250000000 : ℝ))
      (E := (cell12847 ⟨37, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (82797734340111 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (17452527871 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_38 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (1034546291243 / 1250000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558481896807 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨38, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (1034546291243 / 1250000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558481896807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_39 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (10341211987539 / 12500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116965801727 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨39, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (10341211987539 / 12500000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116965801727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12848_20 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83379900464251 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (279217166419 / 12500000000000 : ℝ))
      (E := (cell12848 ⟨20, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83379900464251 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (279217166419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_21 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83345463076599 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446748276477 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨21, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83345463076599 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446748276477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_22 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83311049864731 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (279218168031 / 12500000000000 : ℝ))
      (E := (cell12848 ⟨22, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83311049864731 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (279218168031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_23 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83276660795891 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446749867417 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨23, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83276660795891 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446749867417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_24 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (20810573959373 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446750672843 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨24, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (20810573959373 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446750672843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_25 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (16641590991423 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233757370313 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨25, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (16641590991423 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233757370313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_26 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (16634727624501 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (27922016977 / 1250000000000 : ℝ))
      (E := (cell12848 ⟨26, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (16634727624501 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (27922016977 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_27 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (3325573812063 / 4000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233765388763 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨27, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (3325573812063 / 4000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233765388763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_28 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (51940672789 / 62500000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233769406027 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨28, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (51940672789 / 62500000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233769406027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_29 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41535415786609 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233773412039 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨29, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41535415786609 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233773412039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_30 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83036610602429 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116888704329 / 50000000000000 : ℝ))
      (E := (cell12848 ⟨30, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83036610602429 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116888704329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_31 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83002413518597 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233781397509 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨31, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83002413518597 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233781397509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_32 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82968240290441 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233785438567 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨32, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82968240290441 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233785438567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_33 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (20733522721711 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (55844735397 / 2500000000000 : ℝ))
      (E := (cell12848 ⟨33, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (20733522721711 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (55844735397 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_34 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82899965276843 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233793447567 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨34, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82899965276843 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233793447567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_35 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (20716465857409 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (223379741713 / 10000000000000 : ℝ))
      (E := (cell12848 ⟨35, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (20716465857409 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (223379741713 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_36 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (3313271412583 / 4000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233801442331 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨36, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (3313271412583 / 4000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233801442331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_37 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41398865450583 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233805464827 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨37, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41398865450583 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233805464827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_38 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82763700159073 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (69806544561 / 3125000000000 : ℝ))
      (E := (cell12848 ⟨38, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82763700159073 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (69806544561 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_39 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (82729693058111 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233813442941 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨39, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (82729693058111 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233813442941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12849_20 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83379891887237 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233619212619 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨20, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83379891887237 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233619212619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_21 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83345454805253 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (223362325193 / 10000000000000 : ℝ))
      (E := (cell12849 ⟨21, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83345454805253 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (223362325193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_22 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41655520949313 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116813630557 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨22, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41655520949313 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116813630557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_23 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41638326567301 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446726248731 / 20000000000000 : ℝ))
      (E := (cell12849 ⟨23, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41638326567301 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446726248731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_24 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (20810572120149 / 25000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233635261187 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨24, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (20810572120149 / 25000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233635261187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_25 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (20801986976047 / 25000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233639258387 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨25, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (20801986976047 / 25000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233639258387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_26 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41586815686563 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233643238033 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨26, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41586815686563 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233643238033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_27 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41569669427661 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233647261131 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨27, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41569669427661 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233647261131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_28 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83105070318851 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558412817897 / 25000000000000 : ℝ))
      (E := (cell12849 ⟨28, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83105070318851 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558412817897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_29 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41535412865977 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233655271489 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨29, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41535412865977 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233655271489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_30 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (10379575632879 / 12500000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (223365926269 / 10000000000000 : ℝ))
      (E := (cell12849 ⟨30, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (10379575632879 / 12500000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (223365926269 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_31 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83002408280647 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279207913171 / 12500000000000 : ℝ))
      (E := (cell12849 ⟨31, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83002408280647 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279207913171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_32 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82968235353521 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446733456769 / 20000000000000 : ℝ))
      (E := (cell12849 ⟨32, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82968235353521 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446733456769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_33 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82934086250537 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116835658209 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨33, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82934086250537 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116835658209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_34 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16579992188147 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233675286859 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨34, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16579992188147 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233675286859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_35 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (8286585939331 / 10000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279209914139 / 12500000000000 : ℝ))
      (E := (cell12849 ⟨35, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (8286585939331 / 10000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279209914139 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_36 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (82831781577617 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558420819601 / 25000000000000 : ℝ))
      (E := (cell12849 ⟨36, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (82831781577617 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558420819601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_37 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (20699431865791 / 25000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116843650161 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨37, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (20699431865791 / 25000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116843650161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_38 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (20690924254903 / 25000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116845660137 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨38, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (20690924254903 / 25000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116845660137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_39 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (4136484510839 / 5000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233695338087 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨39, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (4136484510839 / 5000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233695338087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

end BstLean.Part268
