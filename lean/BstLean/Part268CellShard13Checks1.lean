import BstLean.Part268CellShard13Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12675_20 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (10422676011013 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (901851437 / 40000000000 : ℝ))
      (E := (cell12675 ⟨20, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (10422676011013 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (901851437 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_21 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (16669383452293 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563658148253 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨21, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (16669383452293 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563658148253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_22 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83312450685091 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563659138739 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨22, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83312450685091 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563659138739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_23 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83278008326079 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254640598791 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨23, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83278008326079 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254640598791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_24 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83243590151693 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254644553083 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨24, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83243590151693 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254644553083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_25 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (41604598064683 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563662149059 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨25, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (41604598064683 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563662149059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_26 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83174826226697 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563663139051 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨26, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83174826226697 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563663139051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_27 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (16628096082291 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254656611063 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨27, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (16628096082291 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254656611063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_28 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (5194134915723 / 6250000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127330294081 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨28, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (5194134915723 / 6250000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127330294081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_29 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83071860915133 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127332303383 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨29, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83071860915133 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127332303383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_30 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (10379698396301 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254668610569 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨30, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (10379698396301 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254668610569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_31 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83003337385813 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127336300737 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨31, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83003337385813 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127336300737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_32 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (8296911152993 / 10000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563669145289 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨32, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (8296911152993 / 10000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563669145289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_33 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82934909571499 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563670152411 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨33, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82934909571499 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563670152411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_34 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (41450365739711 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127342285509 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨34, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (41450365739711 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127342285509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_35 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (20716644305689 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254688583459 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨35, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (20716644305689 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254688583459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_36 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82832446770719 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (70459143411 / 3125000000000 : ℝ))
      (E := (cell12675 ⟨36, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82832446770719 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (70459143411 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_37 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82798340092681 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254696588643 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨37, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82798340092681 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254696588643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_38 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (82764257158169 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254700640953 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨38, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (82764257158169 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254700640953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_39 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (41365098968433 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450940925761 / 20000000000000 : ℝ))
      (E := (cell12675 ⟨39, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (41365098968433 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450940925761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12676_20 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (20845349808883 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254504965549 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨20, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (20845349808883 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254504965549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_21 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83346908721017 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (281813625443 / 12500000000000 : ℝ))
      (E := (cell12676 ⟨21, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83346908721017 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (281813625443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_22 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (20828110614083 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254513003727 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨22, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (20828110614083 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254513003727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_23 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (3331120016343 / 4000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127258484933 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨23, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (3331120016343 / 4000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127258484933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_24 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (8324358254501 / 10000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254520963863 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨24, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (8324358254501 / 10000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254520963863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_25 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83209188833071 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563631247271 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨25, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83209188833071 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563631247271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_26 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83174819240359 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254528990243 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨26, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83174819240359 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254528990243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_27 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41570236867321 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254532970167 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨27, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41570236867321 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254532970167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_28 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (1662123045677 / 2000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254536989917 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨28, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (1662123045677 / 2000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254536989917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_29 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83071854856081 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563635248359 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨29, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83071854856081 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563635248359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_30 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41518790709797 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254544982857 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨30, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41518790709797 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254544982857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_31 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (10375416492851 / 12500000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (112727450931 / 5000000000000 : ℝ))
      (E := (cell12676 ⟨31, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (10375416492851 / 12500000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (112727450931 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_32 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (20742276598577 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254552985351 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨32, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (20742276598577 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254552985351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_33 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41467452371417 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254557001589 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨33, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41467452371417 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254557001589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_34 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (10362590869661 / 12500000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (112728050501 / 5000000000000 : ℝ))
      (E := (cell12676 ⟨34, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (10362590869661 / 12500000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (112728050501 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_35 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (8286657300673 / 10000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127282505817 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨35, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (8286657300673 / 10000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127282505817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_36 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (662659542883 / 800000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254569007203 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨36, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (662659542883 / 800000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254569007203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_37 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41399168243799 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254572997267 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨37, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41399168243799 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254572997267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_38 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (3310570154317 / 4000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (140911065053 / 6250000000000 : ℝ))
      (E := (cell12676 ⟨38, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (3310570154317 / 4000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (140911065053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_39 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (82730194941039 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563645255167 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨39, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (82730194941039 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563645255167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12677_20 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83381390384587 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225438145119 / 10000000000000 : ℝ))
      (E := (cell12677 ⟨20, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83381390384587 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225438145119 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_21 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41673450091079 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127192705077 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨21, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41673450091079 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127192705077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_22 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (666499473833 / 800000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (450877889723 / 20000000000000 : ℝ))
      (E := (cell12677 ⟨22, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (666499473833 / 800000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (450877889723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_23 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (16655598498517 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254393453789 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨23, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (16655598498517 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254393453789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_24 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83243574939803 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (281799678651 / 12500000000000 : ℝ))
      (E := (cell12677 ⟨24, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83243574939803 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (281799678651 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_25 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (16641836307643 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127200718279 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨25, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (16641836307643 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127200718279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_26 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41587406127711 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127202710277 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨26, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41587406127711 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127202710277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_27 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (10392558382399 / 12500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127204721231 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨27, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (10392558382399 / 12500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127204721231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_28 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41553072958729 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254413446483 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨28, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41553072958729 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254413446483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_29 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41535924399159 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254417434979 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨29, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41535924399159 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254417434979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_30 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (8303757567003 / 10000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254421468593 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨30, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (8303757567003 / 10000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254421468593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_31 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83003326501017 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254425432229 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨31, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83003326501017 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254425432229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_32 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41484550629931 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (450885888921 / 20000000000000 : ℝ))
      (E := (cell12677 ⟨32, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41484550629931 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (450885888921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_33 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82934899915307 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (140902090541 / 6250000000000 : ℝ))
      (E := (cell12677 ⟨33, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82934899915307 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (140902090541 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_34 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (2590647576133 / 3125000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254437445599 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨34, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (2590647576133 / 3125000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254437445599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_35 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82866568791767 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254441436427 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨35, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82866568791767 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254441436427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_36 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82832438951059 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (28180568507 / 1250000000000 : ℝ))
      (E := (cell12677 ⟨36, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82832438951059 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (28180568507 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_37 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (16559666576701 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254449461259 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨37, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (16559666576701 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254449461259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_38 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82764250558633 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254453496173 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨38, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82764250558633 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254453496173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_39 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (82730191946127 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254457468023 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨39, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (82730191946127 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254457468023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12678_20 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83381381535269 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254257932869 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨20, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83381381535269 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254257932869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_21 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83346891644889 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (14089137059 / 625000000000 : ℝ))
      (E := (cell12678 ⟨21, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83346891644889 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (14089137059 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_22 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (8331242600347 / 10000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127132973971 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨22, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (8331242600347 / 10000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127132973971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_23 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20819496144527 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563567483467 / 25000000000000 : ℝ))
      (E := (cell12678 ⟨23, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20819496144527 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563567483467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_24 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (10405445917009 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254273949117 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨24, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (10405445917009 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254273949117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_25 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20802293561199 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254277938659 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨25, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20802293561199 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254277938659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_26 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (16634961054377 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (140892619097 / 6250000000000 : ℝ))
      (E := (cell12678 ⟨26, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (16634961054377 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (140892619097 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_27 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (16628092077021 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127142955533 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨27, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (16628092077021 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127142955533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_28 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83106139552391 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127144978931 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨28, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83106139552391 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127144978931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_29 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41535921370921 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254293931397 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨29, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41535921370921 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254293931397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_30 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20759392480429 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (450859590151 / 20000000000000 : ℝ))
      (E := (cell12678 ⟨30, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20759392480429 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (450859590151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_31 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41501660530219 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254301959371 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨31, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41501660530219 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254301959371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_32 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82969096126591 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254305958919 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨32, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82969096126591 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254305958919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_33 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41467447544459 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563577487711 / 25000000000000 : ℝ))
      (E := (cell12678 ⟨33, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41467447544459 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563577487711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_34 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20725179479081 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254313936361 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨34, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20725179479081 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254313936361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_35 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20716641144467 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563579493773 / 25000000000000 : ℝ))
      (E := (cell12678 ⟨35, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20716641144467 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563579493773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_36 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82832435042769 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254321950571 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨36, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82832435042769 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254321950571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_37 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82798329280401 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127162990309 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨37, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82798329280401 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127162990309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_38 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41382123630147 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254329948227 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨38, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41382123630147 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254329948227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_39 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (82730188952131 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254333970867 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨39, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (82730188952131 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254333970867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12679_20 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41690686343789 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254134410589 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨20, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41690686343789 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254134410589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_21 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (83346883109209 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (450827688961 / 20000000000000 : ℝ))
      (E := (cell12679 ⟨21, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (83346883109209 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (450827688961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_22 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16662483555873 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563535610847 / 25000000000000 : ℝ))
      (E := (cell12679 ⟨22, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16662483555873 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563535610847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_23 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (10409747083143 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254146468451 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨23, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (10409747083143 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254146468451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_24 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (10405444966727 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254150465221 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨24, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (10405444966727 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254150465221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_25 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (5200572934551 / 6250000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (17610581539 / 781250000000 : ℝ))
      (E := (cell12679 ⟨25, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (5200572934551 / 6250000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (17610581539 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_26 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (83174798289747 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127079222621 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨26, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (83174798289747 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127079222621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_27 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (4157022685619 / 5000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127081217211 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨27, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (4157022685619 / 5000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127081217211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_28 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (83106133188649 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (225416646559 / 10000000000000 : ℝ))
      (E := (cell12679 ⟨28, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (83106133188649 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (225416646559 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_29 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (83071836686653 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (225417048269 / 10000000000000 : ℝ))
      (E := (cell12679 ⟨29, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (83071836686653 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (225417048269 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_30 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (20759391043663 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127087214671 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨30, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (20759391043663 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127087214671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_31 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (83003315621071 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127089241489 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨31, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (83003315621071 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127089241489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_32 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16593818198899 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281772808717 / 12500000000000 : ℝ))
      (E := (cell12679 ⟨32, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16593818198899 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281772808717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_33 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82934890263667 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254186449573 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨33, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82934890263667 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254186449573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_34 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (82900713397493 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254190482307 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨34, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (82900713397493 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254190482307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_35 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (10358320045629 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254194451747 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨35, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (10358320045629 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254194451747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_36 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16566486227101 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (225419847589 / 10000000000000 : ℝ))
      (E := (cell12679 ⟨36, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16566486227101 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (225419847589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_37 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41399162839143 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254202496671 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨37, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41399162839143 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254202496671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_38 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41382121981453 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (70443951741 / 3125000000000 : ℝ))
      (E := (cell12679 ⟨38, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41382121981453 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (70443951741 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_39 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (1654603719181 / 2000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254210470481 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨39, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (1654603719181 / 2000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254210470481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12680_20 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41690681920757 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127005500451 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨20, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41690681920757 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127005500451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_21 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83346874575117 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (45080300291 / 2000000000000 : ℝ))
      (E := (cell12680 ⟨21, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83346874575117 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (45080300291 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_22 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83312409556811 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (90160759731 / 4000000000000 : ℝ))
      (E := (cell12680 ⟨22, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83312409556811 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (90160759731 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_23 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83277968753693 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254022999191 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨23, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83277968753693 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254022999191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_24 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (16648710426607 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127013488761 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨24, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (16648710426607 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127013488761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_25 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (1300143119723 / 1562500000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563507747489 / 25000000000000 : ℝ))
      (E := (cell12680 ⟨25, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (1300143119723 / 1562500000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563507747489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_26 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (8317479130901 / 10000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254034981203 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨26, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (8317479130901 / 10000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254034981203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_27 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41570223520509 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (225403901253 / 10000000000000 : ℝ))
      (E := (cell12680 ⟨27, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41570223520509 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (225403901253 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_28 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83106126826231 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127021514067 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨28, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83106126826231 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127021514067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_29 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83071830632751 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254047030373 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨29, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83071830632751 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254047030373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_30 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41518779214419 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254051021379 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨30, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41518779214419 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254051021379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_31 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83003310182917 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (45081100061 / 2000000000000 : ℝ))
      (E := (cell12680 ⟨31, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83003310182917 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (45081100061 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_32 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41484542931787 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (450811807123 / 20000000000000 : ℝ))
      (E := (cell12680 ⟨32, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41484542931787 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (450811807123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_33 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41467442719777 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (90162520137 / 4000000000000 : ℝ))
      (E := (cell12680 ⟨33, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41467442719777 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (90162520137 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_34 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82900708879761 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563516756209 / 25000000000000 : ℝ))
      (E := (cell12680 ⟨34, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82900708879761 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563516756209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_35 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82866556153259 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127035521139 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨35, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82866556153259 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127035521139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_36 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82832427229267 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254075056517 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨36, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82832427229267 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254075056517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_37 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82798322077161 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127039504709 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨37, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82798322077161 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1127039504709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_38 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (82764240666471 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563520754657 / 25000000000000 : ℝ))
      (E := (cell12680 ⟨38, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (82764240666471 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563520754657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_39 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (20682545741721 / 25000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254087025587 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨39, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (20682545741721 / 25000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254087025587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12681_20 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (3335254199883 / 4000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126943793629 / 50000000000000 : ℝ))
      (E := (cell12681 ⟨20, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (3335254199883 / 4000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126943793629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_21 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41673433021307 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (281736447547 / 12500000000000 : ℝ))
      (E := (cell12681 ⟨21, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41673433021307 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (281736447547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_22 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (83312401335807 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253895597607 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨22, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (83312401335807 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253895597607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_23 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (16655592168751 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563474896109 / 25000000000000 : ℝ))
      (E := (cell12681 ⟨23, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (16655592168751 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563474896109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_24 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (83243544533729 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (56347590069 / 2500000000000 : ℝ))
      (E := (cell12681 ⟨24, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (83243544533729 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (56347590069 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_25 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (16641830474633 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253907597549 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨25, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (16641830474633 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253907597549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_26 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (83174784329671 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126955785929 / 50000000000000 : ℝ))
      (E := (cell12681 ⟨26, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (83174784329671 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126955785929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_27 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (10392555046377 / 12500000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253915586953 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨27, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (10392555046377 / 12500000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253915586953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_28 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41553060232569 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253919587029 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨28, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41553060232569 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253919587029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_29 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (16614364916027 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253923574447 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨29, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (16614364916027 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253923574447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_30 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (5189847042767 / 6250000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (450785521969 / 20000000000000 : ℝ))
      (E := (cell12681 ⟨30, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (5189847042767 / 6250000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (450785521969 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_31 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41501652372987 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563482894531 / 25000000000000 : ℝ))
      (E := (cell12681 ⟨31, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41501652372987 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563482894531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_32 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82969080733827 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253935597999 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨32, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82969080733827 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253935597999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_33 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82934880616577 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253939612403 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨33, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82934880616577 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253939612403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_34 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (8290070436313 / 10000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253943622549 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨34, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (8290070436313 / 10000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253943622549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_35 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82866551942549 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253947629427 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨35, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82866551942549 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253947629427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_36 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (16566484664811 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253951633801 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨36, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (16566484664811 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253951633801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_37 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82798318477023 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253955636213 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨37, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82798318477023 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253955636213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_38 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82764237370987 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (140872477311 / 6250000000000 : ℝ))
      (E := (cell12681 ⟨38, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82764237370987 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (140872477311 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_39 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (82730179975633 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253963636187 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨39, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (82730179975633 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253963636187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12682_20 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83381346154263 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253764227933 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨20, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83381346154263 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253764227933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_21 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41673428755849 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450753640117 / 20000000000000 : ℝ))
      (E := (cell12682 ⟨21, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41673428755849 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450753640117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_22 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (1301756142443 / 1562500000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (112688609903 / 5000000000000 : ℝ))
      (E := (cell12682 ⟨22, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (1301756142443 / 1562500000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (112688609903 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_23 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (2602436029229 / 3125000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253776224189 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨23, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (2602436029229 / 3125000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253776224189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_24 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (10405442116987 / 12500000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126890112099 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨24, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (10405442116987 / 12500000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126890112099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_25 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (16641829017099 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (112689210069 / 5000000000000 : ℝ))
      (E := (cell12682 ⟨25, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (16641829017099 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (112689210069 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_26 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83174777351731 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126894108603 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨26, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83174777351731 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126894108603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_27 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (10392554212797 / 12500000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (225379221613 / 10000000000000 : ℝ))
      (E := (cell12682 ⟨27, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (10392554212797 / 12500000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (225379221613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_28 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (10388264263171 / 12500000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253796200741 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨28, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (10388264263171 / 12500000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253796200741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_29 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41535909264403 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126900115943 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨29, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41535909264403 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126900115943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_30 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20759386735239 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253804253251 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨30, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20759386735239 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253804253251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_31 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83003299310243 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (11269041041 / 500000000000 : ℝ))
      (E := (cell12682 ⟨31, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83003299310243 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (11269041041 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_32 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (16593815121051 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253812215447 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨32, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (16593815121051 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253812215447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_33 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41467437897369 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563454054481 / 25000000000000 : ℝ))
      (E := (cell12682 ⟨33, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41467437897369 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563454054481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_34 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (82900699847599 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450764043369 / 20000000000000 : ℝ))
      (E := (cell12682 ⟨34, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (82900699847599 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450764043369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_35 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41433273866451 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (90152970873 / 4000000000000 : ℝ))
      (E := (cell12682 ⟨35, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41433273866451 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (90152970873 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_36 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20708104854967 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253828266397 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨36, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20708104854967 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253828266397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_37 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (662386519023 / 800000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126916129851 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨37, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (662386519023 / 800000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126916129851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_38 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (16552846815291 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253836252059 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨38, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (16552846815291 / 20000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253836252059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_39 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (5170636061581 / 6250000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253840243559 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨39, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (5170636061581 / 6250000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253840243559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12683_20 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (3335253492523 / 4000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126820432327 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨20, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (3335253492523 / 4000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126820432327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_21 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83346848982369 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126822437589 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨21, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83346848982369 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126822437589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_22 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (5207024056153 / 6250000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253648852957 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨22, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (5207024056153 / 6250000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253648852957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_23 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83277945028413 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126826430051 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨23, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83277945028413 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126826430051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_24 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (41621764669769 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126828450103 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨24, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (41621764669769 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126828450103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_25 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83209137799261 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126830429921 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨25, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83209137799261 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126830429921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_26 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (8317477037519 / 10000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253664858831 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨26, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (8317477037519 / 10000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253664858831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_27 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83140427035097 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (70427153127 / 3125000000000 : ℝ))
      (E := (cell12683 ⟨27, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83140427035097 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (70427153127 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_28 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83106107746921 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253672869271 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨28, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83106107746921 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253672869271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_29 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83071812478763 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253676885717 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨29, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83071812478763 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253676885717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_30 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (10379692649861 / 12500000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (70427527909 / 3125000000000 : ℝ))
      (E := (cell12683 ⟨30, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (10379692649861 / 12500000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (70427527909 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_31 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83003293875723 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (14085530583 / 625000000000 : ℝ))
      (E := (cell12683 ⟨31, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83003293875723 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (14085530583 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_32 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (2592783452433 / 3125000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253688887961 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨32, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (2592783452433 / 3125000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253688887961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_33 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (16586974194807 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253692878573 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨33, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (16586974194807 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253692878573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_34 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82900695333167 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126848462467 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨34, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82900695333167 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126848462467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_35 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (20716635881079 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126850455423 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨35, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (20716635881079 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126850455423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_36 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (41416207758353 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253704895651 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨36, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (41416207758353 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253704895651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_37 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (41399155639857 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126854469283 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨37, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (41399155639857 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126854469283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_38 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (41382115391437 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (140857057661 / 6250000000000 : ℝ))
      (E := (cell12683 ⟨38, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (41382115391437 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (140857057661 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_39 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (82730173995873 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253716906427 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨39, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (82730173995873 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253716906427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12684_20 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (10422666059189 / 12500000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253517555697 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨20, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (10422666059189 / 12500000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253517555697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_21 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83346840454627 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (450704309171 / 20000000000000 : ℝ))
      (E := (cell12684 ⟨21, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83346840454627 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (450704309171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_22 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (20828094170523 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253525562303 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨22, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (20828094170523 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253525562303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_23 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (8327793712301 / 10000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563382387631 / 25000000000000 : ℝ))
      (E := (cell12684 ⟨23, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (8327793712301 / 10000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563382387631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_24 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83243521744653 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126766786207 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨24, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83243521744653 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126766786207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_25 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83209130514463 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126768786469 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨25, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83209130514463 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126768786469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_26 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83174763400047 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253541555151 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨26, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83174763400047 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253541555151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_27 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83140420369179 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253545580313 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨27, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83140420369179 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253545580313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_28 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83106101389797 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126774796311 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨28, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83106101389797 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126774796311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_29 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (16614361286001 / 20000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253553594431 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨29, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (16614361286001 / 20000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253553594431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_30 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (20759383864517 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563389396967 / 25000000000000 : ℝ))
      (E := (cell12684 ⟨30, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (20759383864517 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563389396967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_31 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83003288442413 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (225356157483 / 10000000000000 : ℝ))
      (E := (cell12684 ⟨31, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83003288442413 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (225356157483 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_32 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (8296906535163 / 10000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126782807771 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨32, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (8296906535163 / 10000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126782807771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_33 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (20733716538617 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (45071391887 / 2000000000000 : ℝ))
      (E := (cell12684 ⟨33, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (20733716538617 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (45071391887 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_34 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82900690819833 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253573629609 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨34, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82900690819833 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253573629609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_35 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82866539316793 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253577605117 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨35, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82866539316793 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253577605117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_36 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82832411614569 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253581580219 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨36, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82832411614569 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253581580219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_37 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82798307682541 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253585614127 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨37, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82798307682541 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253585614127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_38 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (82764227490243 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253589589829 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨38, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (82764227490243 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253589589829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_39 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (20682542751841 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253593624791 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨39, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (20682542751841 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253593624791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12685_20 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41690659817787 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253394301063 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨20, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41690659817787 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253394301063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_21 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (10418353991059 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253398329219 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨21, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (10418353991059 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253398329219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_22 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (16662473693457 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (140837645381 / 6250000000000 : ℝ))
      (E := (cell12685 ⟨22, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (16662473693457 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (140837645381 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_23 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83277929219117 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253406295457 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨23, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83277929219117 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253406295457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_24 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83243514151241 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (563352574799 / 25000000000000 : ℝ))
      (E := (cell12685 ⟨24, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83243514151241 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (563352574799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_25 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (832091232311 / 1000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253414340669 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨25, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (832091232311 / 1000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253414340669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_26 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41587378213151 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253418306167 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨26, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41587378213151 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253418306167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_27 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (4157020685231 / 5000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253422315323 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨27, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (4157020685231 / 5000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253422315323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_28 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (20776523758499 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (281678289041 / 12500000000000 : ℝ))
      (E := (cell12685 ⟨28, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (20776523758499 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (281678289041 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_29 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (20767950095633 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253430299539 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨29, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (20767950095633 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253430299539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_30 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (16607505943699 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253434337593 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨30, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (16607505943699 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253434337593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_31 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41501641505157 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126719155693 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨31, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41501641505157 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126719155693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_32 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41484530113289 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (140840146227 / 6250000000000 : ℝ))
      (E := (cell12685 ⟨32, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41484530113289 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (140840146227 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_33 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82934861336037 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (90137852267 / 4000000000000 : ℝ))
      (E := (cell12685 ⟨33, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82934861336037 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (90137852267 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_34 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82900686307599 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253450330869 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨34, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82900686307599 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253450330869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_35 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82866535110331 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253454354641 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨35, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82866535110331 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253454354641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_36 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (5177025482091 / 6250000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253458320101 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨36, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (5177025482091 / 6250000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253458320101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_37 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (16559660817271 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450692469013 / 20000000000000 : ℝ))
      (E := (cell12685 ⟨37, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (16559660817271 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450692469013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_38 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (82764224198563 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253466371219 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨38, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (82764224198563 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253466371219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_39 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (10341271002471 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (563367584983 / 25000000000000 : ℝ))
      (E := (cell12685 ⟨39, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (10341271002471 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (563367584983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12686_20 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83381310799259 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450654220151 / 20000000000000 : ℝ))
      (E := (cell12686 ⟨20, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83381310799259 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450654220151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_21 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41673411701951 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (17603711331 / 781250000000 : ℝ))
      (E := (cell12686 ⟨21, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41673411701951 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (17603711331 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_22 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41656180127013 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450655817203 / 20000000000000 : ℝ))
      (E := (cell12686 ⟨22, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41656180127013 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450655817203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_23 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41638960658367 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126641547451 / 50000000000000 : ℝ))
      (E := (cell12686 ⟨23, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41638960658367 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126641547451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_24 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41621753279651 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (45065741611 / 2000000000000 : ℝ))
      (E := (cell12686 ⟨24, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41621753279651 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (45065741611 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_25 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (20802278987293 / 25000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253291104641 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨25, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (20802278987293 / 25000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253291104641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_26 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83174749453953 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126647555941 / 50000000000000 : ℝ))
      (E := (cell12686 ⟨26, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83174749453953 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126647555941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_27 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41570203520711 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253299105091 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨27, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41570203520711 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253299105091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_28 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83106088679517 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450660617371 / 20000000000000 : ℝ))
      (E := (cell12686 ⟨28, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83106088679517 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450660617371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_29 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (10383974292043 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126653559009 / 50000000000000 : ℝ))
      (E := (cell12686 ⟨29, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (10383974292043 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126653559009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_30 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (8303752398017 / 10000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253311083751 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨30, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (8303752398017 / 10000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253311083751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_31 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (3320131103177 / 4000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253315102949 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨31, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (3320131103177 / 4000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253315102949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_32 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82969055102699 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253319118789 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨32, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82969055102699 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253319118789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_33 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82934856518741 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253323074129 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨33, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82934856518741 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253323074129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_34 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82900681796463 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (56333177183 / 2500000000000 : ℝ))
      (E := (cell12686 ⟨34, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82900681796463 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (56333177183 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_35 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (8286653090493 / 10000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253331100789 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨35, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (8286653090493 / 10000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253331100789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_36 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (10354050476671 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (70416722353 / 3125000000000 : ℝ))
      (E := (cell12686 ⟨36, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (10354050476671 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (70416722353 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_37 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82798300491157 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253339131377 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨37, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82798300491157 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253339131377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_38 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (82764220907833 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253343090647 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨38, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (82764220907833 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253343090647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_39 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41365082516543 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (225334711057 / 10000000000000 : ℝ))
      (E := (cell12686 ⟨39, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41365082516543 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (225334711057 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12687_20 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (10422662745571 / 12500000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126573948247 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨20, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (10422662745571 / 12500000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126573948247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_21 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41673407440459 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126575942103 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨21, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41673407440459 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126575942103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_22 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41656176021157 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (70411121887 / 3125000000000 : ℝ))
      (E := (cell12687 ⟨22, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41656176021157 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (70411121887 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_23 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41638956707931 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (225315989051 / 10000000000000 : ℝ))
      (E := (cell12687 ⟨23, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41638956707931 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (225315989051 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_24 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16648699793767 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253163858107 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨24, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16648699793767 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253163858107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_25 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83209108668679 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450633572971 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨25, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83209108668679 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450633572971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_26 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41587371241501 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253171913877 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨26, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41587371241501 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253171913877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_27 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41570200189791 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126587945589 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨27, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41570200189791 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126587945589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_28 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (2077652058159 / 2500000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450635983241 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨28, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (2077652058159 / 2500000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450635983241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_29 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83071788291441 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (563295968601 / 25000000000000 : ℝ))
      (E := (cell12687 ⟨29, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83071788291441 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (563295968601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_30 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83037518243093 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126593942427 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨30, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83037518243093 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126593942427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_31 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41501636074873 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253191890983 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨31, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41501636074873 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253191890983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_32 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (10371131247499 / 12500000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253195894457 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨32, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (10371131247499 / 12500000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253195894457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_33 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (82934851702581 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126599948357 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨33, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (82934851702581 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126599948357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_34 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (3316027091457 / 4000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253203898963 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨34, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (3316027091457 / 4000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253203898963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_35 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (8286652670059 / 10000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (225320790219 / 10000000000000 : ℝ))
      (E := (cell12687 ⟨35, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (8286652670059 / 10000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (225320790219 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_36 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (82832399914303 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126605953577 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨36, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (82832399914303 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126605953577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_37 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16559659379389 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253215914391 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨37, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16559659379389 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253215914391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_38 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (82764217618053 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (563304981053 / 25000000000000 : ℝ))
      (E := (cell12687 ⟨38, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (82764217618053 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (563304981053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_39 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (82730162047317 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253223936707 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨39, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (82730162047317 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253223936707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12688_20 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (166762586263 / 200000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126512373281 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨20, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (166762586263 / 200000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126512373281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_21 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (520917539747 / 625000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253028714133 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨21, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (520917539747 / 625000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253028714133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_22 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (1666246876643 / 2000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126516355441 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨22, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (1666246876643 / 2000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126516355441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_23 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (83277905516499 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126518370317 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨23, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (83277905516499 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126518370317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_24 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (130067955281 / 156250000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253040748613 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨24, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (130067955281 / 156250000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253040748613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_25 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (4160455069481 / 5000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126522369051 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨25, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (4160455069481 / 5000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126522369051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_26 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (10396841939181 / 12500000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126524356077 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨26, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (10396841939181 / 12500000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126524356077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_27 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41570196859551 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563263183007 / 25000000000000 : ℝ))
      (E := (cell12688 ⟨27, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41570196859551 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563263183007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_28 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (3324243038981 / 4000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126528370957 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨28, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (3324243038981 / 4000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126528370957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_29 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (83071782247821 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126530372083 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨29, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (83071782247821 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126530372083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_30 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (83037512507261 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126532370453 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨30, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (83037512507261 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126532370453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_31 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (20750816680319 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563267183507 / 25000000000000 : ℝ))
      (E := (cell12688 ⟨31, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (20750816680319 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563267183507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_32 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82969044858457 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253072725197 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨32, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82969044858457 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253072725197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_33 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (20733711721889 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (70408649201 / 3125000000000 : ℝ))
      (E := (cell12688 ⟨33, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (20733711721889 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (70408649201 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_34 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (20725168194371 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126540382901 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨34, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (20725168194371 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126540382901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_35 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82866522497311 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (35204449357 / 1562500000000 : ℝ))
      (E := (cell12688 ⟨35, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82866522497311 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (35204449357 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_36 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41416198008131 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253088754331 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨36, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41416198008131 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253088754331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_37 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (2069957332593 / 2500000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253092752783 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨37, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (2069957332593 / 2500000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253092752783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_38 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82764214329223 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253096754517 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨38, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82764214329223 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253096754517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_39 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (82730159062461 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253100759623 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨39, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (82730159062461 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253100759623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12689_20 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (16676256860011 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (56322539817 / 2500000000000 : ℝ))
      (E := (cell12689 ⟨20, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (16676256860011 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (56322539817 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_21 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41673398919853 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252905598451 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨21, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41673398919853 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252905598451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_22 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41656167811767 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (225290957583 / 10000000000000 : ℝ))
      (E := (cell12689 ⟨22, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41656167811767 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (225290957583 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_23 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (16655579523729 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (90116543477 / 4000000000000 : ℝ))
      (E := (cell12689 ⟨23, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (16655579523729 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (90116543477 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_24 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83243483792317 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252917576953 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨24, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83243483792317 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252917576953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_25 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (16641818822399 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252921607593 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨25, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (16641818822399 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252921607593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_26 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (8317472854529 / 10000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252925623551 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨26, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (8317472854529 / 10000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252925623551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_27 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83140387059981 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (56323240691 / 2500000000000 : ℝ))
      (E := (cell12689 ⟨27, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83140387059981 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (56323240691 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_28 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83106069624011 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252933622447 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨28, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83106069624011 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252933622447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_29 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41535888102743 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (90117504413 / 4000000000000 : ℝ))
      (E := (cell12689 ⟨29, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41535888102743 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (90117504413 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_30 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83037506772677 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126470796697 / 50000000000000 : ℝ))
      (E := (cell12689 ⟨30, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83037506772677 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126470796697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_31 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (16600652258803 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252945632083 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨31, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (16600652258803 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252945632083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_32 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41484519869047 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252949611009 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨32, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41484519869047 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252949611009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_33 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (16586968414733 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126476824351 / 50000000000000 : ℝ))
      (E := (cell12689 ⟨33, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (16586968414733 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126476824351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_34 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82900668269641 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252957629229 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨34, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82900668269641 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252957629229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_35 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (20716629573773 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252961612133 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨35, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (20716629573773 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252961612133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_36 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (16566478423849 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (281620707103 / 12500000000000 : ℝ))
      (E := (cell12689 ⟨36, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (16566478423849 / 20000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (281620707103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_37 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41399144855741 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126484823277 / 50000000000000 : ℝ))
      (E := (cell12689 ⟨37, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41399144855741 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126484823277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_38 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41382105520671 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (281621705033 / 12500000000000 : ℝ))
      (E := (cell12689 ⟨38, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41382105520671 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (281621705033 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_39 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (82730156078517 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252977638041 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨39, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (82730156078517 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252977638041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12690_20 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (10422659433779 / 12500000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126389246563 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨20, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (10422659433779 / 12500000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126389246563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_21 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83346789321477 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126391239429 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨21, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83346789321477 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126391239429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_22 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83312327416463 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252786495233 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨22, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83312327416463 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252786495233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_23 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (832778897223 / 1000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (225279048773 / 10000000000000 : ℝ))
      (E := (cell12690 ⟨23, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (832778897223 / 1000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (225279048773 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_24 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (16648695241253 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (14079965739 / 625000000000 : ℝ))
      (E := (cell12690 ⟨24, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (16648695241253 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (14079965739 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_25 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83209086835803 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563199632931 / 25000000000000 : ℝ))
      (E := (cell12690 ⟨25, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83209086835803 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563199632931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_26 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (2599210049329 / 3125000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (225280253123 / 10000000000000 : ℝ))
      (E := (cell12690 ⟨26, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (2599210049329 / 3125000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (225280253123 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_27 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41570190201109 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126403259787 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨27, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41570190201109 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126403259787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_28 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83106063274817 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126405249671 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨28, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83106063274817 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126405249671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_29 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41535885082217 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252814531371 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨29, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41535885082217 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252814531371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_30 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41518750519669 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252818500831 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨30, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41518750519669 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252818500831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_31 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83003255867963 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252822526613 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨31, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83003255867963 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252822526613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_32 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41484517309451 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563206637973 / 25000000000000 : ℝ))
      (E := (cell12690 ⟨32, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41484517309451 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563206637973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_33 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82934837260909 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126415259761 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨33, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82934837260909 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126415259761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_34 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (5181291485181 / 6250000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252834547851 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨34, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (5181291485181 / 6250000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252834547851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_35 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41433257046967 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252838520673 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨35, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41433257046967 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252838520673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_36 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (331329552893 / 400000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252842555983 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨36, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (331329552893 / 400000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252842555983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_37 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (82798286120229 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252846537029 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨37, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (82798286120229 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252846537029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_38 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (8276420775441 / 10000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252850522751 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨38, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (8276420775441 / 10000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252850522751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_39 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (16546030619097 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (56321364299 / 2500000000000 : ℝ))
      (E := (cell12690 ⟨39, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (16546030619097 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (56321364299 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12691_20 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83381266642031 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (450531089581 / 20000000000000 : ℝ))
      (E := (cell12691 ⟨20, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83381266642031 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (450531089581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_21 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (2604586900151 / 3125000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (56316486799 / 2500000000000 : ℝ))
      (E := (cell12691 ⟨21, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (2604586900151 / 3125000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (56316486799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_22 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83312319210939 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563165867273 / 25000000000000 : ℝ))
      (E := (cell12691 ⟨22, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83312319210939 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563165867273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_23 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (10409735228433 / 12500000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126333721527 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨23, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (10409735228433 / 12500000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126333721527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_24 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83243468621683 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252671455739 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨24, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83243468621683 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252671455739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_25 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (20802269890261 / 25000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252675452103 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨25, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (20802269890261 / 25000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252675452103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_26 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83174714613161 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563169858799 / 25000000000000 : ℝ))
      (E := (cell12691 ⟨26, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83174714613161 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563169858799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_27 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83140373745813 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (90107338651 / 4000000000000 : ℝ))
      (E := (cell12691 ⟨27, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83140373745813 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (90107338651 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_28 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (16621211385389 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252687431063 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨28, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (16621211385389 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252687431063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_29 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (16614352824933 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126345724409 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨29, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (16614352824933 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126345724409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_30 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41518747653623 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126347731609 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨30, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41518747653623 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126347731609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_31 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (1037540630539 / 1250000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563174869039 / 25000000000000 : ℝ))
      (E := (cell12691 ⟨31, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (1037540630539 / 1250000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563174869039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_32 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41484514750441 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563175872323 / 25000000000000 : ℝ))
      (E := (cell12691 ⟨32, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41484514750441 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (563175872323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_33 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41467416224643 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252707445479 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨33, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41467416224643 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252707445479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_34 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82900659257247 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126355731533 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨34, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82900659257247 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126355731533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_35 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (16573301978767 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126357742237 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨35, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (16573301978767 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126357742237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_36 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41416192164139 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252719510463 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨36, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41416192164139 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252719510463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_37 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41399141264981 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126361741443 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨37, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41399141264981 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126361741443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_38 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (82764204468427 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126363730341 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨38, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (82764204468427 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126363730341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_39 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (16546030022673 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126365751331 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨39, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (16546030022673 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126365751331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12692_20 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20845314453863 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (140783274921 / 6250000000000 : ℝ))
      (E := (cell12692 ⟨20, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20845314453863 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (140783274921 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_21 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (8334677228977 / 10000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126268201427 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨21, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (8334677228977 / 10000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126268201427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_22 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83312311006961 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126270219541 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨22, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83312311006961 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126270219541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_23 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16655574786827 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (70392014153 / 3125000000000 : ℝ))
      (E := (cell12692 ⟨23, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16655574786827 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (70392014153 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_24 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20810865259643 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281568555977 / 12500000000000 : ℝ))
      (E := (cell12692 ⟨24, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20810865259643 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281568555977 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_25 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41604536143859 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252552427123 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨25, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41604536143859 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252552427123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_26 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83174707649189 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563139113071 / 25000000000000 : ℝ))
      (E := (cell12692 ⟨26, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83174707649189 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563139113071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_27 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16628073418153 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (22525604093 / 1000000000000 : ℝ))
      (E := (cell12692 ⟨27, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16628073418153 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (22525604093 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_28 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (10388256322549 / 12500000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252564417613 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨28, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (10388256322549 / 12500000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252564417613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_29 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83071758086179 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450513684231 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨29, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83071758086179 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450513684231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_30 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41518744788199 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126286211023 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨30, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41518744788199 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126286211023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_31 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20750811254871 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (70393013193 / 3125000000000 : ℝ))
      (E := (cell12692 ⟨31, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20750811254871 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (70393013193 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_32 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (2592782012001 / 3125000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252580423207 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨32, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (2592782012001 / 3125000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252580423207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_33 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41467413819399 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252584426571 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨33, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41467413819399 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252584426571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_34 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16580130950539 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252588433477 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨34, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16580130950539 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252588433477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_35 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16573301138959 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450518488981 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨35, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16573301138959 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450518488981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_36 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82832380434329 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (225259646161 / 10000000000000 : ℝ))
      (E := (cell12692 ⟨36, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82832380434329 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (225259646161 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_37 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (82798278940681 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563150121031 / 25000000000000 : ℝ))
      (E := (cell12692 ⟨37, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (82798278940681 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563150121031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_38 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (2586381286981 / 3125000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281575556757 / 12500000000000 : ℝ))
      (E := (cell12692 ⟨38, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (2586381286981 / 3125000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281575556757 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_39 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41365073566079 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126304244433 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨39, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41365073566079 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126304244433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12693_20 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (83381248990493 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252409462179 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨20, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (83381248990493 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252409462179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_21 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (20836690944073 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252413446443 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨21, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (20836690944073 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252413446443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_22 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (5207018925283 / 6250000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252417463529 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨22, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (5207018925283 / 6250000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252417463529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_23 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (16655573208463 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252421458909 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨23, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (16655573208463 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252421458909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_24 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (83243453456931 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252425436103 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨24, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (83243453456931 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252425436103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_25 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (3328362600633 / 4000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252429456787 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨25, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (3328362600633 / 4000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252429456787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_26 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (83174700686613 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126216732829 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨26, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (83174700686613 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126216732829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_27 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (3325614417483 / 4000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126218732767 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨27, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (3325614417483 / 4000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126218732767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_28 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (2077651105879 / 2500000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252441458991 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨28, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (2077651105879 / 2500000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252441458991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_29 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (3322870081959 / 4000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252445448383 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨29, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (3322870081959 / 4000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252445448383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_30 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (20759370961699 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126224717913 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨30, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (20759370961699 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126224717913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_31 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (83003239597057 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126226740873 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨31, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (83003239597057 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126226740873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_32 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82969019268353 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252457470757 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨32, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82969019268353 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252457470757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_33 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41467411414721 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252461462803 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨33, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41467411414721 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252461462803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_34 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82900650249239 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (140779091193 / 6250000000000 : ℝ))
      (E := (cell12693 ⟨34, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82900650249239 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (140779091193 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_35 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (16573300299363 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563117365149 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨35, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (16573300299363 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563117365149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_36 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41416188270701 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252473468079 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨36, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41416188270701 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252473468079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_37 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (16559655070477 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252477482069 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨37, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (16559655070477 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252477482069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_38 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41382098949653 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126240751437 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨38, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41382098949653 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126240751437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_39 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (82730144151861 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (450497094371 / 20000000000000 : ℝ))
      (E := (cell12693 ⟨39, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (82730144151861 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (450497094371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12694_20 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (16676248033431 / 20000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (11261432317 / 500000000000 : ℝ))
      (E := (cell12694 ⟨20, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (16676248033431 / 20000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (11261432317 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_21 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (20836688816099 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252290486129 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨21, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (20836688816099 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252290486129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_22 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83312294603641 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252294484109 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨22, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83312294603641 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252294484109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_23 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83277858152001 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563074629861 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨23, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83277858152001 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563074629861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_24 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83243445876759 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252302478973 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨24, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83243445876759 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252302478973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_25 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83209057745363 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (22523064827 / 1000000000000 : ℝ))
      (E := (cell12694 ⟨25, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83209057745363 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (22523064827 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_26 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (8317469372543 / 10000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126155237661 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨26, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (8317469372543 / 10000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126155237661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_27 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41570176892371 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126157259047 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨27, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41570176892371 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126157259047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_28 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41553018945623 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (70384953023 / 3125000000000 : ℝ))
      (E := (cell12694 ⟨28, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41553018945623 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (70384953023 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_29 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41535873006527 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126161265251 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨29, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41535873006527 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126161265251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_30 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41518739059219 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (28154081307 / 1250000000000 : ℝ))
      (E := (cell12694 ⟨30, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41518739059219 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (28154081307 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_31 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (20750808543959 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252330537797 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨31, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (20750808543959 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252330537797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_32 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (16593802830769 / 20000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (90093380593 / 4000000000000 : ℝ))
      (E := (cell12694 ⟨32, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (16593802830769 / 20000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (90093380593 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_33 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (4146740901061 / 5000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252338495589 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨33, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (4146740901061 / 5000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252338495589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_34 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41450322873439 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (22523425399 / 1000000000000 : ℝ))
      (E := (cell12694 ⟨34, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41450322873439 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (22523425399 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_35 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41433248649947 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563086632887 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨35, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41433248649947 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563086632887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_36 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (10354046581187 / 12500000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (140771908117 / 6250000000000 : ℝ))
      (E := (cell12694 ⟨36, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (10354046581187 / 12500000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (140771908117 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_37 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41399135882537 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252354535399 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨37, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41399135882537 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252354535399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_38 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (10345524327021 / 12500000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126179274219 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨38, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (10345524327021 / 12500000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126179274219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_39 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (20682535293119 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252362510349 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨39, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (20682535293119 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252362510349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12695_20 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41690615672719 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126081788617 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨20, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41690615672719 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126081788617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_21 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83346746754083 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252167580211 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨21, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83346746754083 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252167580211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_22 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41656143202149 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252171559149 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨22, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41656143202149 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252171559149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_23 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (16655570052639 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (45043511523 / 2000000000000 : ℝ))
      (E := (cell12695 ⟨23, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (16655570052639 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (45043511523 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_24 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83243438298057 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126089788213 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨24, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83243438298057 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126089788213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_25 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41604525238167 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126091781629 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨25, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41604525238167 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126091781629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_26 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41587343382821 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252187598111 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨26, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41587343382821 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252187598111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_27 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41570173566883 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252191566981 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨27, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41570173566883 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252191566981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_28 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (20776507887163 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (225219558931 / 10000000000000 : ℝ))
      (E := (cell12695 ⟨28, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (20776507887163 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (225219558931 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_29 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41535869989207 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126099804513 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨29, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41535869989207 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126099804513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_30 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (3321498895653 / 4000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (281525446217 / 12500000000000 : ℝ))
      (E := (cell12695 ⟨30, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (3321498895653 / 4000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (281525446217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_31 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83003228755823 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252207590327 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨31, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83003228755823 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252207590327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_32 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41484504520253 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (225221161397 / 10000000000000 : ℝ))
      (E := (cell12695 ⟨32, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41484504520253 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (225221161397 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_33 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82934813214131 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126107791757 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨33, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82934813214131 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126107791757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_34 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41450320622807 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126109808653 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨34, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41450320622807 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126109808653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_35 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82866493104031 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252223599133 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨35, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82866493104031 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252223599133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_36 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82832368758613 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126113794167 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨36, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82832368758613 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126113794167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_37 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82798268178747 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252231585437 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨37, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82798268178747 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252231585437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_38 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41382095666989 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (563058897687 / 25000000000000 : ℝ))
      (E := (cell12695 ⟨38, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41382095666989 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (563058897687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_39 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (82730138194001 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252239604351 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨39, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (82730138194001 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252239604351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12696_20 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (4169061126267 / 5000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252040687127 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨20, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (4169061126267 / 5000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252040687127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_21 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (10418342280669 / 12500000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252044670391 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨21, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (10418342280669 / 12500000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252044670391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_22 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83312278206499 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252048688651 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨22, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83312278206499 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252048688651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_23 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16655568475179 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252052687381 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨23, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16655568475179 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252052687381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_24 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83243430720823 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126028335047 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨24, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83243430720823 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126028335047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_25 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16641808641747 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450412139693 / 20000000000000 : ℝ))
      (E := (cell12696 ⟨25, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16641808641747 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450412139693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_26 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (5198417487953 / 6250000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (225206471719 / 10000000000000 : ℝ))
      (E := (cell12696 ⟨26, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (5198417487953 / 6250000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (225206471719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_27 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16628068096829 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126034364541 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨27, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16628068096829 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126034364541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_28 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83106025207377 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (563018169563 / 25000000000000 : ℝ))
      (E := (cell12696 ⟨28, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83106025207377 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (563018169563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_29 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16614346789011 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252076683957 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨29, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16614346789011 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252076683957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_30 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (5189841666591 / 6250000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252080689869 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨30, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (5189841666591 / 6250000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252080689869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_31 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83003223337017 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (563021174469 / 25000000000000 : ℝ))
      (E := (cell12696 ⟨31, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83003223337017 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (563021174469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_32 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (82969003928337 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252088709637 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨32, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (82969003928337 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252088709637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_33 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41467404204087 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252092726581 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨33, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41467404204087 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252092726581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_34 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16580127349089 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126048374957 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨34, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16580127349089 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126048374957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_35 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41433244454613 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252100721983 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨35, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41433244454613 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252100721983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_36 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (13253178379 / 16000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126052351061 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨36, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (13253178379 / 16000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126052351061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_37 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16559652918681 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252108749539 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨37, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16559652918681 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252108749539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_38 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16552837610547 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126056373603 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨38, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16552837610547 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126056373603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_39 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (82730135216437 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252116753863 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨39, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (82730135216437 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252116753863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12697_20 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41690606853431 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562979462839 / 25000000000000 : ℝ))
      (E := (cell12697 ⟨20, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41690606853431 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562979462839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_21 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41673364869101 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225192181497 / 10000000000000 : ℝ))
      (E := (cell12697 ⟨21, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41673364869101 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225192181497 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_22 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (20828067502561 / 25000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125962936307 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨22, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (20828067502561 / 25000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125962936307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_23 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83277834490101 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (450385970627 / 20000000000000 : ℝ))
      (E := (cell12697 ⟨23, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83277834490101 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (450385970627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_24 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83243423145059 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125966938359 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨24, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83243423145059 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125966938359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_25 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83209035942567 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562984457481 / 25000000000000 : ℝ))
      (E := (cell12697 ⟨25, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83209035942567 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562984457481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_26 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41587336425123 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125970916281 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨26, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41587336425123 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125970916281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_27 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83140333835881 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225194582907 / 10000000000000 : ℝ))
      (E := (cell12697 ⟨27, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83140333835881 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225194582907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_28 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (4155300943371 / 5000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251949880493 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨28, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (4155300943371 / 5000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251949880493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_29 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41535863956489 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225195387227 / 10000000000000 : ℝ))
      (E := (cell12697 ⟨29, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41535863956489 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225195387227 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_30 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83037460940831 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251957864957 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨30, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83037460940831 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251957864957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_31 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83003217919417 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251961860443 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨31, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83003217919417 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251961860443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_32 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82968998817337 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125982930191 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨32, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82968998817337 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125982930191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_33 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82934803603349 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251969866207 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨33, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82934803603349 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251969866207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_34 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82900632246371 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251973879119 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨34, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82900632246371 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251973879119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_35 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (2071662117887 / 2500000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (35187154689 / 1562500000000 : ℝ))
      (E := (cell12697 ⟨35, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (2071662117887 / 2500000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (35187154689 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_36 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82832360979909 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562995467809 / 25000000000000 : ℝ))
      (E := (cell12697 ⟨36, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82832360979909 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562995467809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_37 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82798261009047 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (45039718207 / 2000000000000 : ℝ))
      (E := (cell12697 ⟨37, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82798261009047 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (45039718207 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_38 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (82764184772439 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251989900413 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨38, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (82764184772439 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251989900413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_39 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (10341266529973 / 12500000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (3518740469 / 156250000000 : ℝ))
      (E := (cell12697 ⟨39, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (10341266529973 / 12500000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (3518740469 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12698_20 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83381204890003 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125897505823 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨20, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83381204890003 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125897505823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_21 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41673360616317 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (45035980279 / 2000000000000 : ℝ))
      (E := (cell12698 ⟨21, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41673360616317 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (45035980279 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_22 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (20828065453883 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450360610543 / 20000000000000 : ℝ))
      (E := (cell12698 ⟨22, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (20828065453883 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450360610543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_23 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83277826605813 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450361403013 / 20000000000000 : ℝ))
      (E := (cell12698 ⟨23, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83277826605813 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450361403013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_24 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41621707785381 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125905510593 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨24, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41621707785381 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125905510593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_25 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (8320902867783 / 10000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251815016031 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨25, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (8320902867783 / 10000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251815016031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_26 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41587332947319 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251819061061 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨26, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41587332947319 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251819061061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_27 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (20785081797243 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (70369470071 / 3125000000000 : ℝ))
      (E := (cell12698 ⟨27, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (20785081797243 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (70369470071 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_28 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83106012528781 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125913510319 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨28, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83106012528781 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125913510319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_29 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83071721882181 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251831056991 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨29, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83071721882181 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251831056991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_30 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83037455217449 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562958759123 / 25000000000000 : ℝ))
      (E := (cell12698 ⟨30, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83037455217449 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562958759123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_31 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (5187700781439 / 6250000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251839078029 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨31, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (5187700781439 / 6250000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251839078029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_32 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41484496853753 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (225184306621 / 10000000000000 : ℝ))
      (E := (cell12698 ⟨32, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41484496853753 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (225184306621 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_33 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (16586959759931 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (140740441311 / 6250000000000 : ℝ))
      (E := (cell12698 ⟨33, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (16586959759931 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (140740441311 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_34 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82900627748391 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251851063529 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨34, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82900627748391 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251851063529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_35 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82866480522791 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450371014969 / 20000000000000 : ℝ))
      (E := (cell12698 ⟨35, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82866480522791 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450371014969 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_36 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (10354044636511 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251859095677 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨36, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (10354044636511 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251859095677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_37 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (10349782178209 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125931533937 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨37, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (10349782178209 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125931533937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_38 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (8276418149309 / 10000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251867050369 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨38, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (8276418149309 / 10000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251867050369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_39 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (82730129264041 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251871101967 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨39, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (82730129264041 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251871101967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12699_20 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41690598037381 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251672226277 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨20, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41690598037381 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251672226277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_21 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41673356364323 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562919066833 / 25000000000000 : ℝ))
      (E := (cell12699 ⟨21, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41673356364323 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562919066833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_22 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (20828063405591 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450336045791 / 20000000000000 : ℝ))
      (E := (cell12699 ⟨22, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (20828063405591 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450336045791 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_23 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83277818723031 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251684231521 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨23, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83277818723031 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251684231521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_24 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83243407997933 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125844139307 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨24, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83243407997933 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125844139307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_25 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83209021414523 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251692256789 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨25, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83209021414523 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251692256789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_26 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83174658940423 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450339257171 / 20000000000000 : ℝ))
      (E := (cell12699 ⟨26, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83174658940423 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450339257171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_27 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41570160271709 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251700251807 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨27, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41570160271709 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251700251807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_28 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (4155300309573 / 5000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562926068521 / 25000000000000 : ℝ))
      (E := (cell12699 ⟨28, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (4155300309573 / 5000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562926068521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_29 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (16614343170533 / 20000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251708296609 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨29, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (16614343170533 / 20000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251708296609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_30 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (8303744949531 / 10000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125856131493 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨30, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (8303744949531 / 10000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125856131493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_31 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (20750801771959 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (22517162921 / 1000000000000 : ℝ))
      (E := (cell12699 ⟨31, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (20750801771959 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (22517162921 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_32 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (20742247149711 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251720268559 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨32, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (20742247149711 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251720268559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_33 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41467396998547 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (281465538861 / 12500000000000 : ℝ))
      (E := (cell12699 ⟨33, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41467396998547 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (281465538861 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_34 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41450311625753 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (281466037893 / 12500000000000 : ℝ))
      (E := (cell12699 ⟨34, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41450311625753 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (281466037893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_35 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82866476331159 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125866152431 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨35, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82866476331159 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125866152431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_36 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82832353205287 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251736316793 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨36, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82832353205287 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251736316793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_37 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41399126921641 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450348056157 / 20000000000000 : ℝ))
      (E := (cell12699 ⟨37, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41399126921641 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450348056157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_38 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (2586380569209 / 3125000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (90069772579 / 4000000000000 : ℝ))
      (E := (cell12699 ⟨38, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (2586380569209 / 3125000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (90069772579 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_39 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (82730126289207 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251748300563 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨39, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (82730126289207 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251748300563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

end BstLean.Part268
