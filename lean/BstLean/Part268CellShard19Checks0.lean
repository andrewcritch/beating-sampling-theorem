import BstLean.Part268CellShard19Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12825_0 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (84074117713497 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447276392787 / 20000000000000 : ℝ))
      (E := (cell12825 ⟨0, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (84074117713497 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (447276392787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_1 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (84039182421877 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236385984039 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨1, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (84039182421877 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236385984039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_2 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (210010680021 / 250000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (111819500383 / 5000000000000 : ℝ))
      (E := (cell12825 ⟨2, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (210010680021 / 250000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (111819500383 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_3 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (8396938643669 / 10000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118196992779 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨3, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (8396938643669 / 10000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118196992779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_4 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83934525670561 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118198991987 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨4, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83934525670561 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118198991987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_5 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (16779937934803 / 20000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236402011049 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨5, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (16779937934803 / 20000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236402011049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_6 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83864878411247 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (34943844011 / 1562500000000 : ℝ))
      (E := (cell12825 ⟨6, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83864878411247 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (34943844011 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_7 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20957522961659 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118205004249 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨7, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20957522961659 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118205004249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_8 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83795329944751 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118206996869 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨8, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83795329944751 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118206996869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_9 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83760592670343 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236417979479 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨9, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83760592670343 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236417979479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_10 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83725879988349 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118210986263 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨10, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83725879988349 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118210986263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_11 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83691191863889 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279553247429 / 12500000000000 : ℝ))
      (E := (cell12825 ⟨11, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83691191863889 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (279553247429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_12 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (16731305652453 / 20000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236430006503 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨12, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (16731305652453 / 20000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236430006503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_13 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83621889148957 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236434001673 / 100000000000000 : ℝ))
      (E := (cell12825 ⟨13, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83621889148957 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (2236434001673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_14 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20896818622407 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (69888688401 / 3125000000000 : ℝ))
      (E := (cell12825 ⟨14, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20896818622407 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (69888688401 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_15 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20888171062529 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (17891536283 / 800000000000 : ℝ))
      (E := (cell12825 ⟨15, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20888171062529 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (17891536283 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_16 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83518118396439 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118223013277 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨16, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83518118396439 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118223013277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_17 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (20870894223697 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118225003691 / 50000000000000 : ℝ))
      (E := (cell12825 ⟨17, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (20870894223697 / 25000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (1118225003691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_18 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (83449059711531 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559113510217 / 25000000000000 : ℝ))
      (E := (cell12825 ⟨18, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (83449059711531 / 100000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559113510217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12825_19 : CellCertificate 12825 (441615566752293 / 5000000000000000 : ℝ) (1637766970200113 / 1000000000000000000 : ℝ) (66148812357929 / 2000000000000000 : ℝ)
    (cell12825 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · norm_num [cell12825]
  · have h := gap_lower (n := 12825) (a := (8341456681321 / 10000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559114503769 / 25000000000000 : ℝ))
      (E := (cell12825 ⟨19, by decide⟩).energy) (xi := (66148812357929 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12825 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12825]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12825])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12825) (a := (8341456681321 / 10000000000000 : ℝ)) (b := (78412877 / 48828125000 : ℝ)) (q := (559114503769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12825])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12825]

theorem cert12826_0 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (84074102879241 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118131588301 / 50000000000000 : ℝ))
      (E := (cell12826 ⟨0, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (84074102879241 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118131588301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_1 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (42019583951431 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559066806817 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨1, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (42019583951431 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559066806817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_2 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (42002128902091 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236271224347 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨2, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (42002128902091 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236271224347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_3 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (10496171568353 / 12500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559068808579 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨3, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (10496171568353 / 12500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559068808579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_4 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41967256047301 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559069801913 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨4, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41967256047301 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559069801913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_5 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83899676411523 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559070802591 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨5, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83899676411523 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559070802591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_6 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83864865461779 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559071798093 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨6, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83864865461779 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559071798093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_7 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (10478759901219 / 12500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118145609611 / 50000000000000 : ℝ))
      (E := (cell12826 ⟨7, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (10478759901219 / 12500000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118145609611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_8 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83795317620011 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236295240279 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨8, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83795317620011 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236295240279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_9 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83760580657309 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236299204563 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨9, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83760580657309 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236299204563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_10 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83725868286583 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236303234923 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨10, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83725868286583 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236303234923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_11 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41845590236477 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236307221821 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨11, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41845590236477 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236307221821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_12 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (3346260687269 / 4000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447262245919 / 20000000000000 : ℝ))
      (E := (cell12826 ⟨12, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (3346260687269 / 4000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447262245919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_13 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83621878378377 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236315206177 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨13, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83621878378377 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236315206177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_14 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41793632014287 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118159607729 / 50000000000000 : ℝ))
      (E := (cell12826 ⟨14, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41793632014287 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (1118159607729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_15 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (20888168524539 / 25000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559080815751 / 25000000000000 : ℝ))
      (E := (cell12826 ⟨15, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (20888168524539 / 25000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (559080815751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_16 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (83518108553139 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447265447549 / 20000000000000 : ℝ))
      (E := (cell12826 ⟨16, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (83518108553139 / 100000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (447265447549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_17 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (41741783679859 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (111816563053 / 5000000000000 : ℝ))
      (E := (cell12826 ⟨17, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (41741783679859 / 50000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (111816563053 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_18 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (4172452524213 / 5000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236335221299 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨18, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (4172452524213 / 5000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236335221299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12826_19 : CellCertificate 12826 (6900029055497 / 78125000000000 : ℝ) (818819618728447 / 500000000000000000 : ℝ) (330717658666419 / 10000000000000000 : ℝ)
    (cell12826 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · norm_num [cell12826]
  · have h := gap_lower (n := 12826) (a := (20853639473327 / 25000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236339239453 / 100000000000000 : ℝ))
      (E := (cell12826 ⟨19, by decide⟩).energy) (xi := (330717658666419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12826 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12826]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12826])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12826) (a := (20853639473327 / 25000000000000 : ℝ)) (b := (40144225473 / 25000000000000 : ℝ)) (q := (2236339239453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12826])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12826]

theorem cert12827_0 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (84074088047301 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118072221259 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨0, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (84074088047301 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118072221259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_1 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (672313227089 / 800000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118074232981 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨1, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (672313227089 / 800000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118074232981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_2 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (21001060900551 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118076218269 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨2, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (21001060900551 / 25000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118076218269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_3 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (2099233966479 / 2500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (279519559827 / 12500000000000 : ℝ))
      (E := (cell12827 ⟨3, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (2099233966479 / 2500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (279519559827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_4 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83934498520809 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236160484827 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨4, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83934498520809 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236160484827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_5 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83899663151157 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236164463239 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨5, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83899663151157 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236164463239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_6 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (104831065643 / 125000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (17889347837 / 800000000000 : ℝ))
      (E := (cell12827 ⟨6, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (104831065643 / 125000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (17889347837 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_7 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83830066574919 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236172483629 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨7, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83830066574919 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236172483629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_8 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (16759061059457 / 20000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118088241277 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨8, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (16759061059457 / 20000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118088241277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_9 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83760568646251 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (447236096691 / 20000000000000 : ℝ))
      (E := (cell12827 ⟨9, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83760568646251 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (447236096691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_10 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (16745171317351 / 20000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236184493133 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨10, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (16745171317351 / 20000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236184493133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_11 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (1046139613549 / 1250000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236188460061 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨11, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (1046139613549 / 1250000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236188460061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_12 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83656506103049 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236192506679 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨12, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83656506103049 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236192506679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_13 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (10452733451203 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (447239292947 / 20000000000000 : ℝ))
      (E := (cell12827 ⟨13, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (10452733451203 / 12500000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (447239292947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_14 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (8358725356931 / 10000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (11181002281 / 500000000000 : ℝ))
      (E := (cell12827 ⟨14, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (8358725356931 / 10000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (11181002281 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_15 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83552663947947 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118102243319 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨15, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83552663947947 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118102243319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_16 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41759049355777 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (89448340127 / 4000000000000 : ℝ))
      (E := (cell12827 ⟨16, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41759049355777 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (89448340127 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_17 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (41741778913163 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118106255409 / 50000000000000 : ℝ))
      (E := (cell12827 ⟨17, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (41741778913163 / 50000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (1118106255409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_18 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (8344904125863 / 10000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (447243302867 / 20000000000000 : ℝ))
      (E := (cell12827 ⟨18, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (8344904125863 / 10000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (447243302867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12827_19 : CellCertificate 12827 (176635261760569 / 2000000000000000 : ℝ) (1637511524636387 / 1000000000000000000 : ℝ) (165345629903309 / 5000000000000000 : ℝ)
    (cell12827 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · norm_num [cell12827]
  · have h := gap_lower (n := 12827) (a := (83414548975011 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236220518251 / 100000000000000 : ℝ))
      (E := (cell12827 ⟨19, by decide⟩).energy) (xi := (165345629903309 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12827 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12827]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12827])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12827) (a := (83414548975011 / 100000000000000 : ℝ)) (b := (160564233699 / 100000000000000 : ℝ)) (q := (2236220518251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12827])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12827]

theorem cert12828_0 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (21018518304419 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559006440421 / 25000000000000 : ℝ))
      (E := (cell12828 ⟨0, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (21018518304419 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559006440421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_1 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (42019569435833 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236029757967 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨1, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (42019569435833 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236029757967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_2 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (16800845880493 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236033759973 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨2, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (16800845880493 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236033759973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_3 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83969344773697 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236037718461 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨3, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83969344773697 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236037718461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_4 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83934484949179 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (447208351517 / 20000000000000 : ℝ))
      (E := (cell12828 ⟨4, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83934484949179 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (447208351517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_5 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41949824946459 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118022884837 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨5, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41949824946459 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118022884837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_6 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (8386483956911 / 10000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118024881269 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨6, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (8386483956911 / 10000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118024881269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_7 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41915026971069 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118026871867 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨7, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41915026971069 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118026871867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_8 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (20948823244143 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236057720567 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨8, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (20948823244143 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236057720567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_9 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (5235034789823 / 6250000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118030879061 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨9, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (5235034789823 / 6250000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118030879061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_10 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41862922444433 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559016436789 / 25000000000000 : ℝ))
      (E := (cell12828 ⟨10, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41862922444433 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (559016436789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_11 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83691157696787 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236069752233 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨11, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83691157696787 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236069752233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_12 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (20914123756559 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118036889827 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨12, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (20914123756559 / 25000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118036889827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_13 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (41810928421349 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236077777349 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨13, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (41810928421349 / 50000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236077777349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_14 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (16717448622367 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118040875529 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨14, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (16717448622367 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118040875529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_15 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83552653799491 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (44721715289 / 2000000000000 : ℝ))
      (E := (cell12828 ⟨15, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83552653799491 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (44721715289 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_16 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (16703617774337 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236089764647 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨16, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (16703617774337 / 20000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236089764647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_17 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83483548294611 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118046878329 / 50000000000000 : ℝ))
      (E := (cell12828 ⟨17, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83483548294611 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (1118046878329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_18 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (1043112900433 / 1250000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236097803491 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨18, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (1043112900433 / 1250000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236097803491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12828_19 : CellCertificate 12828 (883148902601309 / 10000000000000000 : ℝ) (409345957933483 / 250000000000000000 : ℝ) (330664865209131 / 10000000000000000 : ℝ)
    (cell12828 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · norm_num [cell12828]
  · have h := gap_lower (n := 12828) (a := (83414540058317 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236101793207 / 100000000000000 : ℝ))
      (E := (cell12828 ⟨19, by decide⟩).energy) (xi := (330664865209131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12828 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12828]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12828])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12828) (a := (83414540058317 / 100000000000000 : ℝ)) (b := (40137891879 / 25000000000000 : ℝ)) (q := (2236101793207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12828])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12828]

theorem cert12829_0 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (42037029195183 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447181403691 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨0, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (42037029195183 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447181403691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_1 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (21009781089871 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (6987222017 / 312500000000 : ℝ))
      (E := (cell12829 ⟨1, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (21009781089871 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (6987222017 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_2 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (16800843040993 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447183004209 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨2, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (16800843040993 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447183004209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_3 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (16793866178087 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235919069637 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨3, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (16793866178087 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235919069637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_4 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (327869028827 / 390625000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235923025927 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨4, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (327869028827 / 390625000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235923025927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_5 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (20974909159201 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (558981767933 / 25000000000000 : ℝ))
      (E := (cell12829 ⟨5, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (20974909159201 / 25000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (558981767933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_6 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83864826625907 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (279491380139 / 12500000000000 : ℝ))
      (E := (cell12829 ⟨6, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83864826625907 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (279491380139 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_7 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41915020655703 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117967528763 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨7, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41915020655703 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117967528763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_8 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (5237205041117 / 6250000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117969535169 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨8, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (5237205041117 / 6250000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117969535169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_9 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41880272315031 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117971543299 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨9, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41880272315031 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117971543299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_10 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (16745166638583 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235947055051 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨10, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (16745166638583 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235947055051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_11 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (16738229262311 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235951040257 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨11, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (16738229262311 / 20000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235951040257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_12 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83656483951287 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235955048519 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨12, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83656483951287 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235955048519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_13 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83621846077597 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (558989771473 / 25000000000000 : ℝ))
      (E := (cell12829 ⟨13, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83621846077597 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (558989771473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_14 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83587232656149 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447192620007 / 20000000000000 : ℝ))
      (E := (cell12829 ⟨14, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83587232656149 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (447192620007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_15 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41776321826393 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235967096441 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨15, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41776321826393 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235967096441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_16 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83518079033529 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (55899277009 / 2500000000000 : ℝ))
      (E := (cell12829 ⟨16, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83518079033529 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (55899277009 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_17 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41741769382287 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117987528399 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨17, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41741769382287 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117987528399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_18 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (83449022812291 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117989544383 / 50000000000000 : ℝ))
      (E := (cell12829 ⟨18, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (83449022812291 / 100000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (1117989544383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12829_19 : CellCertificate 12829 (883121500498043 / 10000000000000000 : ℝ) (409314039686217 / 250000000000000000 : ℝ) (330638474872847 / 10000000000000000 : ℝ)
    (cell12829 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · norm_num [cell12829]
  · have h := gap_lower (n := 12829) (a := (41707265571613 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235983064321 / 100000000000000 : ℝ))
      (E := (cell12829 ⟨19, by decide⟩).energy) (xi := (330638474872847 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12829 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12829]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12829])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12829) (a := (41707265571613 / 50000000000000 : ℝ)) (b := (160538903343 / 100000000000000 : ℝ)) (q := (2235983064321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12829])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12829]

theorem cert12830_0 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (84074043565371 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (22357883863 / 1000000000000 : ℝ))
      (E := (cell12830 ⟨0, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (84074043565371 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (22357883863 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_1 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (42019554924789 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235792386227 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨1, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (42019554924789 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235792386227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_2 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (10500525126213 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117898196681 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨2, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (10500525126213 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117898196681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_3 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (26870181443 / 32000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235800358463 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨3, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (26870181443 / 32000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235800358463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_4 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83934457812409 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (447160881137 / 20000000000000 : ℝ))
      (E := (cell12830 ⟨4, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83934457812409 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (447160881137 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_5 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (16779924676563 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558952092353 / 25000000000000 : ℝ))
      (E := (cell12830 ⟨5, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (16779924676563 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558952092353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_6 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (10483101710599 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (223581237331 / 10000000000000 : ℝ))
      (E := (cell12830 ⟨6, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (10483101710599 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (223581237331 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_7 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (3353201147309 / 4000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235816367017 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨7, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (3353201147309 / 4000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235816367017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_8 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (16759053668237 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117910207923 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨8, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (16759053668237 / 20000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117910207923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_9 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83760532624929 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558956102713 / 25000000000000 : ℝ))
      (E := (cell12830 ⟨9, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83760532624929 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558956102713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_10 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83725821498901 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117914208409 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨10, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83725821498901 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117914208409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_11 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41845567464111 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (279479047777 / 12500000000000 : ℝ))
      (E := (cell12830 ⟨11, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41845567464111 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (279479047777 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_12 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (418282364391 / 500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558959107371 / 25000000000000 : ℝ))
      (E := (cell12830 ⟨12, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (418282364391 / 500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (558959107371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_13 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (83621835314321 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117920195183 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨13, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (83621835314321 / 100000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117920195183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_14 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (334348888809 / 400000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (223584438683 / 10000000000000 : ℝ))
      (E := (cell12830 ⟨14, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (334348888809 / 400000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (223584438683 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_15 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (10444079188479 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235848424439 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨15, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (10444079188479 / 12500000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235848424439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_16 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (2609939662409 / 3125000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235852392117 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨16, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (2609939662409 / 3125000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235852392117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_17 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41741764618107 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117928205621 / 50000000000000 : ℝ))
      (E := (cell12830 ⟨17, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41741764618107 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (1117928205621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_18 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41724506795791 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (447172085681 / 20000000000000 : ℝ))
      (E := (cell12830 ⟨18, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41724506795791 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (447172085681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12830_19 : CellCertificate 12830 (220773525623021 / 2500000000000000 : ℝ) (1637128505664539 / 1000000000000000000 : ℝ) (20663255549791 / 625000000000000 : ℝ)
    (cell12830 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · norm_num [cell12830]
  · have h := gap_lower (n := 12830) (a := (41707261114869 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235864448127 / 100000000000000 : ℝ))
      (E := (cell12830 ⟨19, by decide⟩).energy) (xi := (20663255549791 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12830 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12830]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12830])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12830) (a := (41707261114869 / 50000000000000 : ℝ)) (b := (8026312059 / 5000000000000 : ℝ)) (q := (2235864448127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12830])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12830]

theorem cert12831_0 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (84074028742689 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279458718697 / 12500000000000 : ℝ))
      (E := (cell12831 ⟨0, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (84074028742689 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279458718697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_1 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (21009773835487 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117836861241 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨1, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (21009773835487 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117836861241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_2 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (84004186816681 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235677761187 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨2, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (84004186816681 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235677761187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_3 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (41984651565257 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (69865054957 / 3125000000000 : ℝ))
      (E := (cell12831 ⟨3, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (41984651565257 / 50000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (69865054957 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_4 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20983611061817 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279460715389 / 12500000000000 : ℝ))
      (E := (cell12831 ⟨4, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20983611061817 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (279460715389 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_5 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83899610130951 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235689778597 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨5, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83899610130951 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235689778597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_6 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20966200186441 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117846879567 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨6, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20966200186441 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117846879567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_7 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20957504014023 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235697730197 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨7, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20957504014023 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235697730197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_8 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83795256026509 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (447140351419 / 20000000000000 : ℝ))
      (E := (cell12831 ⟨8, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83795256026509 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (447140351419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_9 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (20940130155443 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235705788917 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨9, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (20940130155443 / 25000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235705788917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_10 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (10465726225853 / 12500000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235709774401 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨10, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (10465726225853 / 12500000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235709774401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_11 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83691123546789 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (223571377811 / 10000000000000 : ℝ))
      (E := (cell12831 ⟨11, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83691123546789 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (223571377811 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_12 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (653566107867 / 781250000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117858874119 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨12, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (653566107867 / 781250000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117858874119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_13 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (8362182455287 / 10000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117860874449 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨13, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (8362182455287 / 10000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117860874449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_14 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (4179360587507 / 5000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117862892947 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨14, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (4179360587507 / 5000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117862892947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_15 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83552623364629 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117864903309 / 50000000000000 : ℝ))
      (E := (cell12831 ⟨15, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83552623364629 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (1117864903309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_16 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (2087951484059 / 2500000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235733758117 / 100000000000000 : ℝ))
      (E := (cell12831 ⟨16, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (2087951484059 / 2500000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (2235733758117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_17 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (8348351970953 / 10000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (223573776177 / 10000000000000 : ℝ))
      (E := (cell12831 ⟨17, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (8348351970953 / 10000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (223573776177 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_18 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (2607781386641 / 3125000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (447148352833 / 20000000000000 : ℝ))
      (E := (cell12831 ⟨18, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (2607781386641 / 3125000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (447148352833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12831_19 : CellCertificate 12831 (220766677145617 / 2500000000000000 : ℝ) (51156277265259 / 31250000000000000 : ℝ) (330585706979449 / 10000000000000000 : ℝ)
    (cell12831 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · norm_num [cell12831]
  · have h := gap_lower (n := 12831) (a := (83414513317853 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (89429830793 / 4000000000000 : ℝ))
      (E := (cell12831 ⟨19, by decide⟩).energy) (xi := (330585706979449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12831 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12831]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12831])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12831) (a := (83414513317853 / 100000000000000 : ℝ)) (b := (80256790513 / 50000000000000 : ℝ)) (q := (89429830793 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12831])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12831]

theorem cert12832_0 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (1050925174029 / 1250000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235551166107 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨0, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (1050925174029 / 1250000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235551166107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_1 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (42019540418297 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117777556027 / 50000000000000 : ℝ))
      (E := (cell12832 ⟨1, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (42019540418297 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117777556027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_2 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (16800834525179 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235559124521 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨2, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (16800834525179 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235559124521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_3 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83969289253853 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558890788583 / 25000000000000 : ℝ))
      (E := (cell12832 ⟨3, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83969289253853 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558890788583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_4 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (655737739721 / 781250000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (55889178799 / 2500000000000 : ℝ))
      (E := (cell12832 ⟨4, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (655737739721 / 781250000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (55889178799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_5 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20974899220303 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447114225093 / 20000000000000 : ℝ))
      (E := (cell12832 ⟨5, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20974899220303 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447114225093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_6 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83864787808823 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117787570311 / 50000000000000 : ℝ))
      (E := (cell12832 ⟨6, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83864787808823 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117787570311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_7 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83830003431509 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447115829413 / 20000000000000 : ℝ))
      (E := (cell12832 ⟨7, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83830003431509 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447115829413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_8 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20948810928461 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (69861973503 / 3125000000000 : ℝ))
      (E := (cell12832 ⟨8, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20948810928461 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (69861973503 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_9 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20940127155147 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235587162761 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨9, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20940127155147 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235587162761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_10 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83725798116683 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (111779559293 / 5000000000000 : ℝ))
      (E := (cell12832 ⟨10, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83725798116683 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (111779559293 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_11 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (16738222433451 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (111779758493 / 5000000000000 : ℝ))
      (E := (cell12832 ⟨11, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (16738222433451 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (111779758493 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_12 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83656450737613 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117799589547 / 50000000000000 : ℝ))
      (E := (cell12832 ⟨12, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83656450737613 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117799589547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_13 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (20905453448311 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235603161489 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨13, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (20905453448311 / 25000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235603161489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_14 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83587201299817 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235607180929 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨14, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83587201299817 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235607180929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_15 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (10444076652897 / 12500000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447122236961 / 20000000000000 : ℝ))
      (E := (cell12832 ⟨15, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (10444076652897 / 12500000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (447122236961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_16 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (16703609905869 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235615178361 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨16, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (16703609905869 / 20000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235615178361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_17 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (41741755092261 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235619166603 / 100000000000000 : ℝ))
      (E := (cell12832 ⟨17, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (41741755092261 / 50000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (2235619166603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_18 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (83448995155081 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558905788573 / 25000000000000 : ℝ))
      (E := (cell12832 ⟨18, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (83448995155081 / 100000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (558905788573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12832_19 : CellCertificate 12832 (883039318768233 / 10000000000000000 : ℝ) (1636873259211459 / 1000000000000000000 : ℝ) (82639832355029 / 2500000000000000 : ℝ)
    (cell12832 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · norm_num [cell12832]
  · have h := gap_lower (n := 12832) (a := (8341450440757 / 10000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117813602109 / 50000000000000 : ℝ))
      (E := (cell12832 ⟨19, by decide⟩).energy) (xi := (82639832355029 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12832 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12832]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12832])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12832) (a := (8341450440757 / 10000000000000 : ℝ)) (b := (160500922881 / 100000000000000 : ℝ)) (q := (1117813602109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12832])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12832]

theorem cert12833_0 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (10509249888033 / 12500000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235432578071 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨0, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (10509249888033 / 12500000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235432578071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_1 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (42019533166757 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447087310989 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨1, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (42019533166757 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447087310989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_2 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (42002079218673 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235440541237 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨2, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (42002079218673 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235440541237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_3 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83969275379391 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (223544454559 / 10000000000000 : ℝ))
      (E := (cell12833 ⟨3, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83969275379391 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (223544454559 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_4 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (8393441712347 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447089715279 / 20000000000000 : ℝ))
      (E := (cell12833 ⟨4, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (8393441712347 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (447089715279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_5 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (16779916726719 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235452583843 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨5, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (16779916726719 / 20000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235452583843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_6 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83864774873967 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (111772828787 / 5000000000000 : ℝ))
      (E := (cell12833 ⟨6, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83864774873967 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (111772828787 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_7 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41914995404487 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117730279819 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨7, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41914995404487 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117730279819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_8 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83795231403191 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (139716537553 / 6250000000000 : ℝ))
      (E := (cell12833 ⟨8, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83795231403191 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (139716537553 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_9 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41880248310689 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (111773429521 / 5000000000000 : ℝ))
      (E := (cell12833 ⟨9, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41880248310689 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (111773429521 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_10 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41862893214239 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117736296569 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨10, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41862893214239 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117736296569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_11 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (4184555039481 / 5000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235476557467 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨11, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (4184555039481 / 5000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235476557467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_12 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (2614263739691 / 3125000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117740302923 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨12, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (2614263739691 / 3125000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117740302923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_13 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41810901517721 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117742285007 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨13, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41810901517721 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117742285007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_14 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (1044839885641 / 1250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117744285969 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨14, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (1044839885641 / 1250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117744285969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_15 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (5222037692717 / 6250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235492617177 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨15, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (5222037692717 / 6250000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235492617177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_16 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (41759019849021 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117748297327 / 50000000000000 : ℝ))
      (E := (cell12833 ⟨16, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (41759019849021 / 50000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (1117748297327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_17 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (8348350066119 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235500625743 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨17, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (8348350066119 / 10000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235500625743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_18 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83448985939289 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558876149697 / 25000000000000 : ℝ))
      (E := (cell12833 ⟨18, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83448985939289 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (558876149697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12833_19 : CellCertificate 12833 (27594122907763 / 312500000000000 : ℝ) (8183728329147 / 5000000000000000 : ℝ) (330532956117549 / 10000000000000000 : ℝ)
    (cell12833 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · norm_num [cell12833]
  · have h := gap_lower (n := 12833) (a := (83414495498889 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235508634773 / 100000000000000 : ℝ))
      (E := (cell12833 ⟨19, by decide⟩).energy) (xi := (330532956117549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12833 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12833]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12833])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12833) (a := (83414495498889 / 100000000000000 : ℝ)) (b := (160488266743 / 100000000000000 : ℝ)) (q := (2235508634773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12833])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12833]

theorem cert12834_0 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (2101849607213 / 2500000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (558828496367 / 25000000000000 : ℝ))
      (E := (cell12834 ⟨0, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (2101849607213 / 2500000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (558828496367 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_1 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (21009762958177 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235317993309 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨1, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (21009762958177 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235317993309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_2 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (84004144251033 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117661005667 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨2, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (84004144251033 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117661005667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_3 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83969261507127 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235325990293 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨3, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83969261507127 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235325990293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_4 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83934403564813 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235329996419 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨4, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83934403564813 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235329996419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_5 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41949785194051 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235334037847 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨5, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41949785194051 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235334037847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_6 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83864761941197 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235338006523 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨6, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83864761941197 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235338006523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_7 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83829978188487 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117671012951 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨7, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83829978188487 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117671012951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_8 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (20948804773637 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (69854563917 / 3125000000000 : ℝ))
      (E := (cell12834 ⟨8, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (20948804773637 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (69854563917 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_9 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (4188024231207 / 5000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (111767500693 / 5000000000000 : ℝ))
      (E := (cell12834 ⟨9, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (4188024231207 / 5000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (111767500693 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_10 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83725774742209 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (558838513573 / 25000000000000 : ℝ))
      (E := (cell12834 ⟨10, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83725774742209 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (558838513573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_11 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83691089413883 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117679028547 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨11, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83691089413883 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117679028547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_12 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83656428604471 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117681014247 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨12, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83656428604471 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117681014247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_13 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (10452724034933 / 12500000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235366032601 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨13, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (10452724034933 / 12500000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235366032601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_14 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (8358718040453 / 10000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235370017069 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨14, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (8358718040453 / 10000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235370017069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_15 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (41776296472759 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (55884351139 / 2500000000000 : ℝ))
      (E := (cell12834 ⟨15, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (41776296472759 / 50000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (55884351139 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_16 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (20879507467113 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235378065193 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨16, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (20879507467113 / 25000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235378065193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_17 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83483491139533 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235382080969 / 100000000000000 : ℝ))
      (E := (cell12834 ⟨17, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83483491139533 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (2235382080969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_18 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (5215561045321 / 6250000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117693019703 / 50000000000000 : ℝ))
      (E := (cell12834 ⟨18, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (5215561045321 / 6250000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (1117693019703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12834_19 : CellCertificate 12834 (441492275711027 / 5000000000000000 : ℝ) (1636618092337459 / 1000000000000000000 : ℝ) (4131332338383 / 125000000000000 : ℝ)
    (cell12834 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · norm_num [cell12834]
  · have h := gap_lower (n := 12834) (a := (83414486591809 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (223539006149 / 10000000000000 : ℝ))
      (E := (cell12834 ⟨19, by decide⟩).energy) (xi := (4131332338383 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12834 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12834]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12834])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12834) (a := (83414486591809 / 100000000000000 : ℝ)) (b := (160475612613 / 100000000000000 : ℝ)) (q := (223539006149 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12834])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12834]

theorem cert12835_0 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (5254623092193 / 6250000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235195503947 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨0, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (5254623092193 / 6250000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235195503947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_1 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (2626219916693 / 3125000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117599742497 / 50000000000000 : ℝ))
      (E := (cell12835 ⟨1, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (2626219916693 / 3125000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117599742497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_2 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (84004130066957 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117601738471 / 50000000000000 : ℝ))
      (E := (cell12835 ⟨2, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (84004130066957 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (1117601738471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_3 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41984623818531 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235207488439 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨3, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41984623818531 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235207488439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_4 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (20983597502079 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235211469951 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨4, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (20983597502079 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235211469951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_5 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (20974889286183 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (55880387187 / 2500000000000 : ℝ))
      (E := (cell12835 ⟨5, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (20974889286183 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (55880387187 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_6 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (5241546813157 / 6250000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235219490937 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨6, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (5241546813157 / 6250000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235219490937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_7 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83829965570047 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235223487873 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨7, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83829965570047 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235223487873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_8 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41897603393957 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (139701717849 / 6250000000000 : ℝ))
      (E := (cell12835 ⟨8, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41897603393957 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (139701717849 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_9 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (670083781031 / 800000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235231491117 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨9, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (670083781031 / 800000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235231491117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_10 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (669806104463 / 800000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235235511267 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨10, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (669806104463 / 800000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235235511267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_11 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (20922769510011 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235239494499 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨11, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (20922769510011 / 25000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235239494499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_12 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83656417540691 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (279405438143 / 12500000000000 : ℝ))
      (E := (cell12835 ⟨12, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83656417540691 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (279405438143 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_13 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83621781525309 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235247549251 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨13, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83621781525309 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235247549251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_14 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83587169959567 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235251516323 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨14, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83587169959567 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235251516323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_15 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83552582809313 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (34925867627 / 1562500000000 : ℝ))
      (E := (cell12835 ⟨15, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83552582809313 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (34925867627 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_16 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (41759010020287 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235259531781 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨16, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (41759010020287 / 50000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235259531781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_17 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (83483481619551 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235263532283 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨17, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (83483481619551 / 100000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235263532283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_18 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (4172448375631 / 5000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558816883599 / 25000000000000 : ℝ))
      (E := (cell12835 ⟨18, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (4172448375631 / 5000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (558816883599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12835_19 : CellCertificate 12835 (110369646736023 / 1250000000000000 : ℝ) (204561317341373 / 125000000000000000 : ℝ) (8262005556957 / 250000000000000 : ℝ)
    (cell12835 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · norm_num [cell12835]
  · have h := gap_lower (n := 12835) (a := (8341447768633 / 10000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235271542639 / 100000000000000 : ℝ))
      (E := (cell12835 ⟨19, by decide⟩).energy) (xi := (8262005556957 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12835 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12835]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12835])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12835) (a := (8341447768633 / 10000000000000 : ℝ)) (b := (16046296049 / 10000000000000 : ℝ)) (q := (2235271542639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12835])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12835]

theorem cert12836_0 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (84073954663967 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235077017863 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨0, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (84073954663967 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235077017863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_1 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (84039022837917 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117540486077 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨1, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (84039022837917 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117540486077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_2 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (16800823177023 / 20000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235084995937 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨2, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (16800823177023 / 20000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235084995937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_3 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41984616884597 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235088982139 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨3, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41984616884597 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235088982139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_4 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83934376453979 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235092996991 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨4, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83934376453979 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235092996991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_5 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83899543903483 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558774247671 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨5, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83899543903483 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558774247671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_6 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (10483092010239 / 12500000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (279387628623 / 12500000000000 : ℝ))
      (E := (cell12836 ⟨6, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (10483092010239 / 12500000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (279387628623 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_7 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (16765990590731 / 20000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235105003537 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨7, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (16765990590731 / 20000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235105003537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_8 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83795194483291 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235109037591 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨8, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83795194483291 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235109037591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_9 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41880230317791 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (139694563887 / 6250000000000 : ℝ))
      (E := (cell12836 ⟨9, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41880230317791 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (139694563887 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_10 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (20931437843869 / 25000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117558511061 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨10, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (20931437843869 / 25000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117558511061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_11 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (41845533334051 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117560521963 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨11, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (41845533334051 / 50000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117560521963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_12 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83656406478771 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235125035797 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨12, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83656406478771 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235125035797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_13 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (5226360673311 / 6250000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235129003711 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨13, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (5226360673311 / 6250000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235129003711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_14 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (20896789879097 / 25000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (447026602311 / 20000000000000 : ℝ))
      (E := (cell12836 ⟨14, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (20896789879097 / 25000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (447026602311 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_15 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83552572674857 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235137006709 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨15, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83552572674857 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235137006709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_16 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83518010214407 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117570526309 / 50000000000000 : ℝ))
      (E := (cell12836 ⟨16, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83518010214407 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (1117570526309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_17 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83483472101243 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558786259477 / 25000000000000 : ℝ))
      (E := (cell12836 ⟨17, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83483472101243 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (558786259477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_18 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (83448958301741 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235149025513 / 100000000000000 : ℝ))
      (E := (cell12836 ⟨18, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (83448958301741 / 100000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (2235149025513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12836_19 : CellCertificate 12836 (441464900222923 / 5000000000000000 : ℝ) (102272687812833 / 62500000000000000 : ℝ) (330453861739363 / 10000000000000000 : ℝ)
    (cell12836 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · norm_num [cell12836]
  · have h := gap_lower (n := 12836) (a := (20853617195613 / 25000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (139697063747 / 6250000000000 : ℝ))
      (E := (cell12836 ⟨19, by decide⟩).energy) (xi := (330453861739363 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12836 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12836]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12836])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12836) (a := (20853617195613 / 25000000000000 : ℝ)) (b := (160450310373 / 100000000000000 : ℝ)) (q := (139697063747 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12836])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12836]

theorem cert12837_0 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (84073939855157 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117479263607 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨0, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (84073939855157 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117479263607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_1 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (84039008343931 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (558740628159 / 25000000000000 : ℝ))
      (E := (cell12837 ⟨1, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (84039008343931 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (558740628159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_2 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (84004101705509 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (558741627611 / 25000000000000 : ℝ))
      (E := (cell12837 ⟨2, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (84004101705509 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (558741627611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_3 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83969219903523 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (446994105857 / 20000000000000 : ℝ))
      (E := (cell12837 ⟨3, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83969219903523 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (446994105857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_4 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83934362901801 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2234974519623 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨4, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83934362901801 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2234974519623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_5 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83899530664357 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117489273729 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨5, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83899530664357 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117489273729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_6 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (16772944631079 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (22349825627 / 1000000000000 : ℝ))
      (E := (cell12837 ⟨6, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (16772944631079 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (22349825627 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_7 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83829940339309 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (69843330403 / 3125000000000 : ℝ))
      (E := (cell12837 ⟨7, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83829940339309 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (69843330403 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_8 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (20948795545169 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (558747631833 / 25000000000000 : ℝ))
      (E := (cell12837 ⟨8, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (20948795545169 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (558747631833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_9 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (4188022432213 / 5000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2234994549051 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨9, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (4188022432213 / 5000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2234994549051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_10 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (8372573969501 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2793748161 / 125000000000 : ℝ))
      (E := (cell12837 ⟨10, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (8372573969501 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2793748161 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_11 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (10461381912257 / 12500000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117501265567 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨11, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (10461381912257 / 12500000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117501265567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_12 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (83656395418711 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235006562347 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨12, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (83656395418711 / 100000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235006562347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_13 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41810880011233 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235010570363 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨13, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41810880011233 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235010570363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_14 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (16717429814999 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235014560911 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨14, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (16717429814999 / 20000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235014560911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_15 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (20888140635537 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235018597653 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨15, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (20888140635537 / 25000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235018597653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_16 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (1304968756093 / 1562500000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (447004513901 / 20000000000000 : ℝ))
      (E := (cell12837 ⟨16, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (1304968756093 / 1562500000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (447004513901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_17 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (8348346258461 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117513298921 / 50000000000000 : ℝ))
      (E := (cell12837 ⟨17, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (8348346258461 / 10000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (1117513298921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_18 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (33379579637 / 40000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235030571001 / 100000000000000 : ℝ))
      (E := (cell12837 ⟨18, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (33379579637 / 40000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (2235030571001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12837_19 : CellCertificate 12837 (882902431094077 / 10000000000000000 : ℝ) (818117745577921 / 500000000000000000 : ℝ) (165213752726391 / 5000000000000000 : ℝ)
    (cell12837 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · norm_num [cell12837]
  · have h := gap_lower (n := 12837) (a := (41707229940087 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (447006921993 / 20000000000000 : ℝ))
      (E := (cell12837 ⟨19, by decide⟩).energy) (xi := (165213752726391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12837 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12837]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12837])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12837) (a := (41707229940087 / 50000000000000 : ℝ)) (b := (160437662263 / 100000000000000 : ℝ)) (q := (447006921993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12837])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12837]

theorem cert12838_0 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (5254620315541 / 6250000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223484008983 / 10000000000000 : ℝ))
      (E := (cell12838 ⟨0, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (5254620315541 / 6250000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223484008983 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_1 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (84038993852217 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234844106443 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨1, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (84038993852217 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234844106443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_2 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (10500510941017 / 12500000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (111742403917 / 5000000000000 : ℝ))
      (E := (cell12838 ⟨2, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (10500510941017 / 12500000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (111742403917 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_3 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83969206040049 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (55871303247 / 2500000000000 : ℝ))
      (E := (cell12838 ⟨3, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83969206040049 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (55871303247 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_4 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41967174675891 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446971219153 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨4, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41967174675891 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446971219153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_5 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83899517427351 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446972019973 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨5, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83899517427351 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446972019973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_6 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41932355115481 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234864092087 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨6, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41932355115481 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234864092087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_7 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (2619685241469 / 3125000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446973627593 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨7, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (2619685241469 / 3125000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446973627593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_8 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83795169880069 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (558718032211 / 25000000000000 : ℝ))
      (E := (cell12838 ⟨8, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83795169880069 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (558718032211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_9 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (8376043665491 / 10000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223487612973 / 10000000000000 : ℝ))
      (E := (cell12838 ⟨9, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (8376043665491 / 10000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (223487612973 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_10 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83725728016479 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234880147417 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨10, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83725728016479 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234880147417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_11 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83691043929907 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117442065183 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨11, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83691043929907 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117442065183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_12 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83656384360509 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446977628581 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨12, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83656384360509 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446977628581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_13 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41810874636889 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117446066477 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨13, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41810874636889 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117446066477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_14 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83587138635387 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446979221249 / 20000000000000 : ℝ))
      (E := (cell12838 ⟨14, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83587138635387 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (446979221249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_15 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83552552411187 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234900126437 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨15, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83552552411187 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234900126437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_16 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (41758995283603 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117452070323 / 50000000000000 : ℝ))
      (E := (cell12838 ⟨16, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (41758995283603 / 50000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (1117452070323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_17 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (83483453069649 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234908153869 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨17, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (83483453069649 / 100000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234908153869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_18 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (16689787976979 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234912170863 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨18, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (16689787976979 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234912170863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12838_19 : CellCertificate 12838 (220718766457979 / 2500000000000000 : ℝ) (1636107997177879 / 1000000000000000000 : ℝ) (330401153417431 / 10000000000000000 : ℝ)
    (cell12838 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · norm_num [cell12838]
  · have h := gap_lower (n := 12838) (a := (16682890195899 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234916137879 / 100000000000000 : ℝ))
      (E := (cell12838 ⟨19, by decide⟩).energy) (xi := (330401153417431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12838 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12838]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12838])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12838) (a := (16682890195899 / 20000000000000 : ℝ)) (b := (80212508079 / 50000000000000 : ℝ)) (q := (2234916137879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12838])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12838]

theorem cert12839_0 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (16814782048893 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558680426427 / 25000000000000 : ℝ))
      (E := (cell12839 ⟨0, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (16814782048893 / 20000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558680426427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_1 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (42019489681387 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (139670355983 / 6250000000000 : ℝ))
      (E := (cell12839 ⟨1, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (42019489681387 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (139670355983 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_2 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (42002036676499 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117364849811 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨2, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (42002036676499 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117364849811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_3 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83969192178771 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234733726031 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨3, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83969192178771 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234733726031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_4 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83934335803921 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (111736886271 / 5000000000000 : ℝ))
      (E := (cell12839 ⟨4, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83934335803921 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (111736886271 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_5 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41949752096233 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117370852923 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨5, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41949752096233 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117370852923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_6 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (20966174327153 / 25000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234745733073 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨6, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (20966174327153 / 25000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234745733073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_7 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41914957558377 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279343712343 / 12500000000000 : ℝ))
      (E := (cell12839 ⟨7, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41914957558377 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279343712343 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_8 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83795157581471 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279344215763 / 12500000000000 : ℝ))
      (E := (cell12839 ⟨8, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83795157581471 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (279344215763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_9 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (8376042466753 / 10000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234757706197 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨9, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (8376042466753 / 10000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234757706197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_10 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (2093142908497 / 2500000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117380851901 / 50000000000000 : ℝ))
      (E := (cell12839 ⟨10, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (2093142908497 / 2500000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (1117380851901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_11 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41845516281827 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234765725461 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨11, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41845516281827 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234765725461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_12 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41828186652083 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558692429841 / 25000000000000 : ℝ))
      (E := (cell12839 ⟨12, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41828186652083 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558692429841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_13 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83621738526911 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234773749613 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨13, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83621738526911 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234773749613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_14 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83587128197563 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558694426427 / 25000000000000 : ℝ))
      (E := (cell12839 ⟨14, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83587128197563 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558694426427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_15 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83552542281973 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558695427353 / 25000000000000 : ℝ))
      (E := (cell12839 ⟨15, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83552542281973 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (558695427353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_16 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (83517980746171 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234785707839 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨16, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (83517980746171 / 100000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234785707839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_17 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41741721778181 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (139674360263 / 6250000000000 : ℝ))
      (E := (cell12839 ⟨17, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41741721778181 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (139674360263 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_18 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (41724465339463 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446958753371 / 20000000000000 : ℝ))
      (E := (cell12839 ⟨18, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (41724465339463 / 50000000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (446958753371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12839_19 : CellCertificate 12839 (882847704658403 / 10000000000000000 : ℝ) (408995130766699 / 250000000000000000 : ℝ) (330374805632203 / 10000000000000000 : ℝ)
    (cell12839 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · norm_num [cell12839]
  · have h := gap_lower (n := 12839) (a := (2606701315013 / 3125000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234797720227 / 100000000000000 : ℝ))
      (E := (cell12839 ⟨19, by decide⟩).energy) (xi := (330374805632203 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12839 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12839]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12839])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12839) (a := (2606701315013 / 3125000000000 : ℝ)) (b := (80206186029 / 50000000000000 : ℝ)) (q := (2234797720227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12839])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12839]

theorem cert12840_0 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (84073895442583 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117301658513 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨0, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (84073895442583 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117301658513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_1 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (84038964875603 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (111730366917 / 5000000000000 : ℝ))
      (E := (cell12840 ⟨1, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (84038964875603 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (111730366917 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_2 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (21001014795023 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234611316423 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨2, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (21001014795023 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234611316423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_3 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (10496147289961 / 12500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234615317739 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨3, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (10496147289961 / 12500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234615317739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_4 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41967161129109 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (223461935067 / 10000000000000 : ℝ))
      (E := (cell12840 ⟨4, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41967161129109 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (223461935067 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_5 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (83899490959701 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (111731165373 / 5000000000000 : ℝ))
      (E := (cell12840 ⟨5, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (83899490959701 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (111731165373 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_6 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (16772936877669 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (279328413971 / 12500000000000 : ℝ))
      (E := (cell12840 ⟨6, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (16772936877669 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (279328413971 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_7 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (163730278337 / 195312500000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234631313221 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨7, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (163730278337 / 195312500000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234631313221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_8 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (1047439316061 / 1250000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234635319113 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨8, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (1047439316061 / 1250000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234635319113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_9 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (2094010317053 / 2500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446927867297 / 20000000000000 : ℝ))
      (E := (cell12840 ⟨9, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (2094010317053 / 2500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (446927867297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_10 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41862852332607 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234643314071 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨10, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41862852332607 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234643314071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_11 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (1307672206239 / 1562500000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234647316421 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨11, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (1307672206239 / 1562500000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234647316421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_12 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (83656362249681 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (223465134983 / 10000000000000 : ℝ))
      (E := (cell12840 ⟨12, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (83656362249681 / 100000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (223465134983 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_13 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (16724345556373 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234655362213 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨13, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (16724345556373 / 20000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234655362213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_14 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41793558880761 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234659359301 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨14, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41793558880761 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234659359301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_15 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41776266077253 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117331673289 / 50000000000000 : ℝ))
      (E := (cell12840 ⟨15, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41776266077253 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (1117331673289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_16 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41758985463423 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (558666832321 / 25000000000000 : ℝ))
      (E := (cell12840 ⟨16, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41758985463423 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (558666832321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_17 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (20870858511187 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234671370639 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨17, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (20870858511187 / 25000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234671370639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_18 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (41724460737297 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (8729200621 / 390625000000 : ℝ))
      (E := (cell12840 ⟨18, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (41724460737297 / 50000000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (8729200621 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12840_19 : CellCertificate 12840 (27588135861643 / 312500000000000 : ℝ) (1635853068817949 / 1000000000000000000 : ℝ) (165174231047997 / 5000000000000000 : ℝ)
    (cell12840 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · norm_num [cell12840]
  · have h := gap_lower (n := 12840) (a := (10426804147867 / 12500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234679357011 / 100000000000000 : ℝ))
      (E := (cell12840 ⟨19, by decide⟩).energy) (xi := (165174231047997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12840 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12840]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12840])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12840) (a := (10426804147867 / 12500000000000 : ℝ)) (b := (160399729963 / 100000000000000 : ℝ)) (q := (2234679357011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12840])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12840]

theorem cert12841_0 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (84073880643009 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558621245403 / 25000000000000 : ℝ))
      (E := (cell12841 ⟨0, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (84073880643009 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558621245403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_1 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (42019475195351 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234488976433 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨1, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (42019475195351 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234488976433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_2 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (84004045009419 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279311623327 / 12500000000000 : ℝ))
      (E := (cell12841 ⟨2, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (84004045009419 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (279311623327 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_3 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (209922911157 / 250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (22344969629 / 1000000000000 : ℝ))
      (E := (cell12841 ⟨3, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (209922911157 / 250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (22344969629 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_4 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (5245894294667 / 6250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117250485759 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨4, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (5245894294667 / 6250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117250485759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_5 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (2621858679033 / 3125000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558626240663 / 25000000000000 : ℝ))
      (E := (cell12841 ⟨5, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (2621858679033 / 3125000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558626240663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_6 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (83864671470159 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234509002067 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨6, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (83864671470159 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234509002067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_7 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (83829889902379 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234512981399 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨7, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (83829889902379 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234512981399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_8 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (10474391623787 / 12500000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117258482943 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨8, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (10474391623787 / 12500000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117258482943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_9 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (2094010017467 / 2500000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558630240641 / 25000000000000 : ℝ))
      (E := (cell12841 ⟨9, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (2094010017467 / 2500000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558630240641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_10 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (83725692992481 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (89380999129 / 4000000000000 : ℝ))
      (E := (cell12841 ⟨10, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (83725692992481 / 100000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (89380999129 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_11 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41845504918417 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (139658060083 / 6250000000000 : ℝ))
      (E := (cell12841 ⟨11, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41845504918417 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (139658060083 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_12 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41828175598527 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (11172664881 / 500000000000 : ℝ))
      (E := (cell12841 ⟨12, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41828175598527 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (11172664881 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_13 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (1045271462983 / 1250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446907394151 / 20000000000000 : ℝ))
      (E := (cell12841 ⟨13, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (1045271462983 / 1250000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446907394151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_14 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (16717421465453 / 20000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558635252219 / 25000000000000 : ℝ))
      (E := (cell12841 ⟨14, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (16717421465453 / 20000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558635252219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_15 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (16710504405757 / 20000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234544979763 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨15, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (16710504405757 / 20000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234544979763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_16 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (8351796110923 / 10000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446909800997 / 20000000000000 : ℝ))
      (E := (cell12841 ⟨16, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (8351796110923 / 10000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (446909800997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_17 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (41741712267403 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234553031387 / 100000000000000 : ℝ))
      (E := (cell12841 ⟨17, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (41741712267403 / 50000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (2234553031387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_18 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (10431114033987 / 12500000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558639251369 / 25000000000000 : ℝ))
      (E := (cell12841 ⟨18, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (10431114033987 / 12500000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (558639251369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12841_19 : CellCertificate 12841 (220698248643369 / 2500000000000000 : ℝ) (1635725634426697 / 1000000000000000000 : ℝ) (330322122807699 / 10000000000000000 : ℝ)
    (cell12841 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · norm_num [cell12841]
  · have h := gap_lower (n := 12841) (a := (16682884857411 / 20000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117280494983 / 50000000000000 : ℝ))
      (E := (cell12841 ⟨19, by decide⟩).energy) (xi := (330322122807699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12841 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12841]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12841])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12841) (a := (16682884857411 / 20000000000000 : ℝ)) (b := (160387089871 / 100000000000000 : ℝ)) (q := (1117280494983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12841])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12841]

theorem cert12842_0 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (84073865845743 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234366641639 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨0, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (84073865845743 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234366641639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_1 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (84038935908071 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (446874133571 / 20000000000000 : ℝ))
      (E := (cell12842 ⟨1, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (84038935908071 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (446874133571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_2 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (84004030840979 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117187326163 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨2, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (84004030840979 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117187326163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_3 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41984575304053 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117189330757 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨3, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41984575304053 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117189330757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_4 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83934295173283 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (55859566147 / 2500000000000 : ℝ))
      (E := (cell12842 ⟨4, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83934295173283 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (55859566147 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_5 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83899464500529 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234386671421 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨5, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83899464500529 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234386671421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_6 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (16772931710811 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117195315037 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨6, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (16772931710811 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117195315037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_7 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83829877298257 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (223439464529 / 10000000000000 : ℝ))
      (E := (cell12842 ⟨7, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83829877298257 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (223439464529 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_8 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83795120697719 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234398666419 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨8, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83795120697719 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234398666419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_9 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83760388717209 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117201321233 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨9, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83760388717209 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117201321233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_10 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83725681321679 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234406638207 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨10, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83725681321679 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234406638207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_11 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (16738199695253 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234410660183 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨11, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (16738199695253 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234410660183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_12 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (16731268029257 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117207328289 / 50000000000000 : ℝ))
      (E := (cell12842 ⟨12, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (16731268029257 / 20000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (1117207328289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_13 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41810853148617 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (279302336437 / 12500000000000 : ℝ))
      (E := (cell12842 ⟨13, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41810853148617 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (279302336437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_14 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83587096894791 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234422654429 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨14, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83587096894791 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234422654429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_15 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (8355251190481 / 10000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234426667141 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨15, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (8355251190481 / 10000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234426667141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_16 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41758975646661 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234430676743 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨16, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41758975646661 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234430676743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_17 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (10435426878317 / 12500000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558608672057 / 25000000000000 : ℝ))
      (E := (cell12842 ⟨17, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (10435426878317 / 12500000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (558608672057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_18 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (41724451535417 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (139652419147 / 6250000000000 : ℝ))
      (E := (cell12842 ⟨18, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (41724451535417 / 50000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (139652419147 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12842_19 : CellCertificate 12842 (441382822830071 / 5000000000000000 : ℝ) (1635598219888397 / 1000000000000000000 : ℝ) (330295787766213 / 10000000000000000 : ℝ)
    (cell12842 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · norm_num [cell12842]
  · have h := gap_lower (n := 12842) (a := (83414415392771 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234442677359 / 100000000000000 : ℝ))
      (E := (cell12842 ⟨19, by decide⟩).energy) (xi := (330295787766213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12842 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12842]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12842])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12842) (a := (83414415392771 / 100000000000000 : ℝ)) (b := (20046806473 / 12500000000000 : ℝ)) (q := (2234442677359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12842])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12842]

theorem cert12843_0 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (2627307845337 / 3125000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446849670987 / 20000000000000 : ℝ))
      (E := (cell12843 ⟨0, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (2627307845337 / 3125000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446849670987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_1 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (84038921427709 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234252354761 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨1, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (84038921427709 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234252354761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_2 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (8400401667477 / 10000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234256371431 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨2, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (8400401667477 / 10000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234256371431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_3 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41984568377803 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234260355689 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨3, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41984568377803 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234260355689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_4 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (1678685632681 / 2000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (872759521 / 39062500000 : ℝ))
      (E := (cell12843 ⟨4, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (1678685632681 / 2000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (872759521 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_5 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41949725637061 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234268375827 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨5, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41949725637061 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234268375827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_6 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (2620770176251 / 3125000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279284046211 / 12500000000000 : ℝ))
      (E := (cell12843 ⟨6, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (2620770176251 / 3125000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279284046211 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_7 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (83829864696179 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558569090721 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨7, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (83829864696179 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558569090721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_8 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (20948777101787 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117140181353 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨8, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (20948777101787 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117140181353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_9 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41880188368853 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446856875239 / 20000000000000 : ℝ))
      (E := (cell12843 ⟨9, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41880188368853 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446856875239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_10 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (83725669652809 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234288352077 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨10, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (83725669652809 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234288352077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_11 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (83690987117591 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117146177453 / 50000000000000 : ℝ))
      (E := (cell12843 ⟨11, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (83690987117591 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (1117146177453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_12 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (20914082274343 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279287048871 / 12500000000000 : ℝ))
      (E := (cell12843 ⟨12, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (20914082274343 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279287048871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_13 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (83621695557649 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558575087513 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨13, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (83621695557649 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558575087513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_14 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (835870864641 / 1000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234304354117 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨14, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (835870864641 / 1000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234304354117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_15 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (83552501782581 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446861681743 / 20000000000000 : ℝ))
      (E := (cell12843 ⟨15, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (83552501782581 / 100000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (446861681743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_16 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (20879485369781 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558578100689 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨16, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (20879485369781 / 25000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558578100689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_17 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41741702759969 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558579099847 / 25000000000000 : ℝ))
      (E := (cell12843 ⟨17, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41741702759969 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (558579099847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_18 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41724446935703 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234320403363 / 100000000000000 : ℝ))
      (E := (cell12843 ⟨18, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41724446935703 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (2234320403363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12843_19 : CellCertificate 12843 (441369150415807 / 5000000000000000 : ℝ) (1635470825198413 / 1000000000000000000 : ℝ) (5160460265163 / 156250000000000 : ℝ)
    (cell12843 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · norm_num [cell12843]
  · have h := gap_lower (n := 12843) (a := (41707203250043 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279290552399 / 12500000000000 : ℝ))
      (E := (cell12843 ⟨19, by decide⟩).energy) (xi := (5160460265163 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12843 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12843]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12843])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12843) (a := (41707203250043 / 50000000000000 : ℝ)) (b := (160361815699 / 100000000000000 : ℝ)) (q := (279290552399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12843])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12843]

theorem cert12844_0 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (21018459064533 / 25000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558532515919 / 25000000000000 : ℝ))
      (E := (cell12844 ⟨0, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (21018459064533 / 25000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558532515919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_1 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (84038906949617 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234134094997 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨1, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (84038906949617 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234134094997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_2 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (10500500313849 / 12500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117069043029 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨2, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (10500500313849 / 12500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117069043029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_3 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (839691229053 / 1000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234142103319 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨3, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (839691229053 / 1000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234142103319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_4 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83934268096973 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234146097239 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨4, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83934268096973 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234146097239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_5 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (10487429756229 / 12500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (69817189871 / 3125000000000 : ℝ))
      (E := (cell12844 ⟨5, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (10487429756229 / 12500000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (69817189871 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_6 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (8386463272809 / 10000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117077052489 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨6, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (8386463272809 / 10000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117077052489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_7 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (16765970419229 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234158076193 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨7, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (16765970419229 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234158076193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_8 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (41897548059291 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (55854052819 / 2500000000000 : ℝ))
      (E := (cell12844 ⟨8, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (41897548059291 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (55854052819 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_9 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (20940091190043 / 25000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558541526429 / 25000000000000 : ℝ))
      (E := (cell12844 ⟨9, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (20940091190043 / 25000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558541526429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_10 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83725657985869 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234170119837 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨10, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83725657985869 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234170119837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_11 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (8369097576081 / 10000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234174103579 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨11, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (8369097576081 / 10000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234174103579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_12 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (16731263610063 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117089060633 / 50000000000000 : ℝ))
      (E := (cell12844 ⟨12, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (16731263610063 / 20000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (1117089060633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_13 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (41810842409941 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234182120811 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨13, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (41810842409941 / 50000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234182120811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_14 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (8358707603519 / 10000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (111709305397 / 5000000000000 : ℝ))
      (E := (cell12844 ⟨14, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (8358707603519 / 10000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (111709305397 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_15 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (5222030728881 / 6250000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223419014631 / 10000000000000 : ℝ))
      (E := (cell12844 ⟨15, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (5222030728881 / 6250000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (223419014631 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_16 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83517931666633 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234194124829 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨16, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83517931666633 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234194124829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_17 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (8348339601501 / 10000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558549526661 / 25000000000000 : ℝ))
      (E := (cell12844 ⟨17, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (8348339601501 / 10000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (558549526661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_18 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83448884673613 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (8727352167 / 390625000000 : ℝ))
      (E := (cell12844 ⟨18, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83448884673613 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (8727352167 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12844_19 : CellCertificate 12844 (882710960086933 / 10000000000000000 : ℝ) (817671725176053 / 500000000000000000 : ℝ) (165121565209627 / 5000000000000000 : ℝ)
    (cell12844 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · norm_num [cell12844]
  · have h := gap_lower (n := 12844) (a := (83414397608997 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234206157199 / 100000000000000 : ℝ))
      (E := (cell12844 ⟨19, by decide⟩).energy) (xi := (165121565209627 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12844 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12844]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12844])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12844) (a := (83414397608997 / 100000000000000 : ℝ)) (b := (160349181617 / 100000000000000 : ℝ)) (q := (2234206157199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12844])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12844]

theorem cert12845_0 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (84073821467787 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (279251478211 / 12500000000000 : ℝ))
      (E := (cell12845 ⟨0, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (84073821467787 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (279251478211 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_1 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (1313107694903 / 1562500000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (6981299471 / 312500000000 : ℝ))
      (E := (cell12845 ⟨1, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (1313107694903 / 1562500000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (6981299471 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_2 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (16800797669809 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1745328011 / 78125000000 : ℝ))
      (E := (cell12845 ⟨2, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (16800797669809 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1745328011 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_3 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83969109057187 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234023846511 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨3, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83969109057187 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234023846511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_4 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83934254562051 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117013937119 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨4, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83934254562051 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117013937119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_5 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (4194971241383 / 5000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117015914749 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨5, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (4194971241383 / 5000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117015914749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_6 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (20966154954557 / 25000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117017917973 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨6, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (20966154954557 / 25000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117017917973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_7 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83829839498153 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117019921603 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨7, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83829839498153 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117019921603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_8 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83795083832021 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (279255482321 / 12500000000000 : ℝ))
      (E := (cell12845 ⟨8, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83795083832021 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (279255482321 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_9 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (16752070556921 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446809577813 / 20000000000000 : ℝ))
      (E := (cell12845 ⟨9, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (16752070556921 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446809577813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_10 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (4186282316043 / 5000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234051883427 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨10, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (4186282316043 / 5000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234051883427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_11 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83690964405923 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234055848121 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨11, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83690964405923 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234055848121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_12 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (16731261401023 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (223405984747 / 10000000000000 : ℝ))
      (E := (cell12845 ⟨12, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (16731261401023 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (223405984747 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_13 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (16724334816787 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446812777503 / 20000000000000 : ℝ))
      (E := (cell12845 ⟨13, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (16724334816787 / 20000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (446812777503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_14 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83587065608063 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117033928873 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨14, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83587065608063 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117033928873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_15 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (20888120385839 / 25000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117035939963 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨15, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (20888120385839 / 25000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117035939963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_16 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (1670358437117 / 2000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (55851897529 / 2500000000000 : ℝ))
      (E := (cell12845 ⟨16, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (1670358437117 / 2000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (55851897529 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_17 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41741693255877 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (111703993411 / 5000000000000 : ℝ))
      (E := (cell12845 ⟨17, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41741693255877 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (111703993411 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_18 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (83448875477453 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117041951139 / 50000000000000 : ℝ))
      (E := (cell12845 ⟨18, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (83448875477453 / 100000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (1117041951139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12845_19 : CellCertificate 12845 (882683623425141 / 10000000000000000 : ℝ) (40880402383621 / 25000000000000000 : ℝ) (13208672324463 / 400000000000000 : ℝ)
    (cell12845 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · norm_num [cell12845]
  · have h := gap_lower (n := 12845) (a := (41707194359753 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234087891377 / 100000000000000 : ℝ))
      (E := (cell12845 ⟨19, by decide⟩).energy) (xi := (13208672324463 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12845 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12845]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12845])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12845) (a := (41707194359753 / 50000000000000 : ℝ)) (b := (160336549537 / 100000000000000 : ℝ)) (q := (2234087891377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12845])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12845]

theorem cert12846_0 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (84073806679747 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233893640971 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨0, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (84073806679747 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233893640971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_1 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (21009719500059 / 25000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (89355904791 / 4000000000000 : ℝ))
      (E := (cell12846 ⟨1, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (21009719500059 / 25000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (89355904791 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_2 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (10500496773691 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233901617627 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨2, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (10500496773691 / 12500000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233901617627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_3 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41984547605633 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116952821581 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨3, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41984547605633 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116952821581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_4 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83934241029283 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233909646839 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨4, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83934241029283 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233909646839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_5 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (16779882321521 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233913636707 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨5, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (16779882321521 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233913636707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_6 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (16772921382089 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233917620559 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨6, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (16772921382089 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233917620559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_7 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41914913451101 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233921663927 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨7, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41914913451101 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233921663927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_8 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (16759014309493 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233925658143 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨8, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (16759014309493 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233925658143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_9 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41880170405503 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (139620604263 / 6250000000000 : ℝ))
      (E := (cell12846 ⟨9, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41880170405503 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (139620604263 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_10 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83725634657781 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (44678672857 / 2000000000000 : ℝ))
      (E := (cell12846 ⟨10, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83725634657781 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (44678672857 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_11 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (326917785363 / 390625000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233937646617 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨11, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (326917785363 / 390625000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233937646617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_12 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83656295961769 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116970842897 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨12, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83656295961769 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116970842897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_13 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (16724332669961 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116972825083 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨13, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (16724332669961 / 20000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116972825083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_14 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (20896763795679 / 25000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (223394966169 / 10000000000000 : ℝ))
      (E := (cell12846 ⟨14, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (20896763795679 / 25000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (223394966169 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_15 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83552471426361 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (111697683387 / 5000000000000 : ℝ))
      (E := (cell12846 ⟨15, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83552471426361 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (111697683387 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_16 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (41758956023387 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (139622354597 / 6250000000000 : ℝ))
      (E := (cell12846 ⟨16, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (41758956023387 / 50000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (139622354597 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_17 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83483377010167 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233961684117 / 100000000000000 : ℝ))
      (E := (cell12846 ⟨17, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83483377010167 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (2233961684117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_18 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (83448866282927 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (446793140837 / 20000000000000 : ℝ))
      (E := (cell12846 ⟨18, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (83448866282927 / 100000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (446793140837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12846_19 : CellCertificate 12846 (882656290845277 / 10000000000000000 : ℝ) (81754438008599 / 50000000000000000 : ℝ) (82547622511573 / 2500000000000000 : ℝ)
    (cell12846 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · norm_num [cell12846]
  · have h := gap_lower (n := 12846) (a := (20853594957903 / 25000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116984839999 / 50000000000000 : ℝ))
      (E := (cell12846 ⟨19, by decide⟩).energy) (xi := (82547622511573 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12846 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12846]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12846])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12846) (a := (20853594957903 / 25000000000000 : ℝ)) (b := (160323919459 / 100000000000000 : ℝ)) (q := (1116984839999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12846])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12846]

theorem cert12847_0 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (21018447973503 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (446755090341 / 20000000000000 : ℝ))
      (E := (cell12847 ⟨0, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (21018447973503 / 25000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (446755090341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_1 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (84038863528947 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233779462167 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨1, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (84038863528947 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233779462167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_2 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (1050049500403 / 1250000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233783434573 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨2, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (1050049500403 / 1250000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233783434573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_3 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (5248067585471 / 6250000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (111689371769 / 5000000000000 : ℝ))
      (E := (cell12847 ⟨3, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (5248067585471 / 6250000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (111689371769 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_4 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (8393422749867 / 10000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116895736481 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨4, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (8393422749867 / 10000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116895736481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_5 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83899398389667 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233795439557 / 100000000000000 : ℝ))
      (E := (cell12847 ⟨5, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83899398389667 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (2233795439557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_6 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83864594004741 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116899729409 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨6, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83864594004741 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116899729409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_7 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (41914907154147 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116901740183 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨7, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (41914907154147 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116901740183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_8 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (41897529632457 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558451863369 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨8, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (41897529632457 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558451863369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_9 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (41880164419687 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558452860787 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨9, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (41880164419687 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558452860787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_10 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83725622996631 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116907728083 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨10, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83725622996631 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116907728083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_11 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (41845470850913 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116909749533 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨11, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (41845470850913 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116909749533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_12 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83656284920279 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558455865481 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨12, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83656284920279 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558455865481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_13 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (41810826308747 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (446765493379 / 20000000000000 : ℝ))
      (E := (cell12847 ⟨13, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (41810826308747 / 50000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (446765493379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_14 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83587044759151 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (111691573081 / 5000000000000 : ℝ))
      (E := (cell12847 ⟨14, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83587044759151 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (111691573081 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_15 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83552461311109 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558458877439 / 25000000000000 : ℝ))
      (E := (cell12847 ⟨15, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83552461311109 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (558458877439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_16 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (16703580447881 / 20000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116919750103 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨16, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (16703580447881 / 20000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116919750103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_17 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83483367510251 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116921748057 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨17, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83483367510251 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116921748057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_18 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83448857090033 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (279230937779 / 12500000000000 : ℝ))
      (E := (cell12847 ⟨18, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83448857090033 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (279230937779 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12847_19 : CellCertificate 12847 (55164310146649 / 625000000000000 : ℝ) (817480722414447 / 500000000000000000 : ℝ) (10317630506947 / 312500000000000 : ℝ)
    (cell12847 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · norm_num [cell12847]
  · have h := gap_lower (n := 12847) (a := (83414370945313 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116925761533 / 50000000000000 : ℝ))
      (E := (cell12847 ⟨19, by decide⟩).energy) (xi := (10317630506947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12847 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12847]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12847])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12847) (a := (83414370945313 / 100000000000000 : ℝ)) (b := (160311291381 / 100000000000000 : ℝ)) (q := (1116925761533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12847])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12847]

theorem cert12848_0 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (84073777110581 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (17450447779 / 781250000000 : ℝ))
      (E := (cell12848 ⟨0, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (84073777110581 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (17450447779 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_1 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (21009712264981 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233661300047 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨1, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (21009712264981 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233661300047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_2 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (42001972938591 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (558416326229 / 25000000000000 : ℝ))
      (E := (cell12848 ⟨2, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (42001972938591 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (558416326229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_3 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41984533762999 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (69802165033 / 3125000000000 : ℝ))
      (E := (cell12848 ⟨3, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41984533762999 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (69802165033 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_4 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83934213970211 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (69802290459 / 3125000000000 : ℝ))
      (E := (cell12848 ⟨4, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83934213970211 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (69802290459 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_5 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (16779877034769 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233677295991 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨5, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (16779877034769 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233677295991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_6 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (20966145275279 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233681292757 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨6, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (20966145275279 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233681292757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_7 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41914900858213 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (558421323131 / 25000000000000 : ℝ))
      (E := (cell12848 ⟨7, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41914900858213 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (558421323131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_8 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41897523492183 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116844651289 / 50000000000000 : ℝ))
      (E := (cell12848 ⟨8, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41897523492183 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116844651289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_9 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83760316869707 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116846664977 / 50000000000000 : ℝ))
      (E := (cell12848 ⟨9, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83760316869707 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116846664977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_10 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (8372561133741 / 10000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (17869578587 / 800000000000 : ℝ))
      (E := (cell12848 ⟨10, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (8372561133741 / 10000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (17869578587 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_11 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (16738186070523 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (558425336847 / 25000000000000 : ℝ))
      (E := (cell12848 ⟨11, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (16738186070523 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (558425336847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_12 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (20914068470161 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116852675087 / 50000000000000 : ℝ))
      (E := (cell12848 ⟨12, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (20914068470161 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (1116852675087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_13 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83621641887 / 100000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (22337093377 / 1000000000000 : ℝ))
      (E := (cell12848 ⟨13, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83621641887 / 100000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (22337093377 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_14 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (16717406867473 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (223371331569 / 10000000000000 : ℝ))
      (E := (cell12848 ⟨14, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (16717406867473 / 20000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (223371331569 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_15 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (104440563997 / 125000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446743469559 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨15, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (104440563997 / 125000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446743469559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_16 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (41758946216871 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233721322921 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨16, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (41758946216871 / 50000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233721322921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_17 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (83483358012003 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446745072487 / 20000000000000 : ℝ))
      (E := (cell12848 ⟨17, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (83483358012003 / 100000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (446745072487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_18 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (20862211974693 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233729354661 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨18, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (20862211974693 / 25000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233729354661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12848_19 : CellCertificate 12848 (55162602370469 / 625000000000000 : ℝ) (1634834149310949 / 1000000000000000000 : ℝ) (330137866638509 / 10000000000000000 : ℝ)
    (cell12848 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · norm_num [cell12848]
  · have h := gap_lower (n := 12848) (a := (8341436206061 / 10000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233733362309 / 100000000000000 : ℝ))
      (E := (cell12848 ⟨19, by decide⟩).energy) (xi := (330137866638509 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12848 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12848]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12848])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12848) (a := (8341436206061 / 10000000000000 : ℝ)) (b := (32059733061 / 20000000000000 : ℝ)) (q := (2233733362309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12848])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12848]

theorem cert12849_0 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16814752465891 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233539175171 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨0, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16814752465891 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233539175171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_1 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (5252427162073 / 6250000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116771595633 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨1, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (5252427162073 / 6250000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116771595633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_2 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (84003931724351 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233547170789 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨2, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (84003931724351 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233547170789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_3 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83969053686651 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446710236039 / 20000000000000 : ℝ))
      (E := (cell12849 ⟨3, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83969053686651 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446710236039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_4 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16786840088781 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233555169939 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨4, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16786840088781 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233555169939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_5 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41949685980069 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233559206013 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨5, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41949685980069 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233559206013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_6 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83864568199569 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446712636069 / 20000000000000 : ℝ))
      (E := (cell12849 ⟨6, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83864568199569 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446712636069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_7 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (419148945633 / 500000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279195894799 / 12500000000000 : ℝ))
      (E := (cell12849 ⟨7, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (419148945633 / 500000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279195894799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_8 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83795034705821 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558392801363 / 25000000000000 : ℝ))
      (E := (cell12849 ⟨8, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83795034705821 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (558392801363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_9 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83760304902007 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116787606279 / 50000000000000 : ℝ))
      (E := (cell12849 ⟨9, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83760304902007 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (1116787606279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_10 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41862799840059 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (111678959321 / 5000000000000 : ℝ))
      (E := (cell12849 ⟨10, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41862799840059 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (111678959321 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_11 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16738183801059 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446716638317 / 20000000000000 : ℝ))
      (E := (cell12849 ⟨11, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16738183801059 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (446716638317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_12 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41828131421431 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279198397029 / 12500000000000 : ℝ))
      (E := (cell12849 ⟨12, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41828131421431 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (279198397029 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_13 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83621631158323 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233591204457 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨13, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83621631158323 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233591204457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_14 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (1044837798967 / 1250000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (22335952239 / 1000000000000 : ℝ))
      (E := (cell12849 ⟨14, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (1044837798967 / 1250000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (22335952239 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_15 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (41776220542917 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233599181861 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨15, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (41776220542917 / 50000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233599181861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_16 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (16703576525957 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233603199901 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨16, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (16703576525957 / 20000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233603199901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_17 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (3339333940617 / 4000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233607224857 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨17, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (3339333940617 / 4000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233607224857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_18 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (10431104838643 / 12500000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (223361120323 / 10000000000000 : ℝ))
      (E := (cell12849 ⟨18, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (10431104838643 / 12500000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (223361120323 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

theorem cert12849_19 : CellCertificate 12849 (441287158793839 / 5000000000000000 : ℝ) (408676718403379 / 250000000000000000 : ℝ) (165055780646903 / 5000000000000000 : ℝ)
    (cell12849 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · norm_num [cell12849]
  · have h := gap_lower (n := 12849) (a := (83414353177503 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233615197729 / 100000000000000 : ℝ))
      (E := (cell12849 ⟨19, by decide⟩).energy) (xi := (165055780646903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12849 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12849]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12849])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12849) (a := (83414353177503 / 100000000000000 : ℝ)) (b := (40071510307 / 25000000000000 : ℝ)) (q := (2233615197729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12849])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12849]

end BstLean.Part268
