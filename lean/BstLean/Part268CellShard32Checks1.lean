import BstLean.Part268CellShard32Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13150_20 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83376319220097 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199195710751 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨20, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83376319220097 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199195710751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_21 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41670960142777 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099599873533 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨21, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41670960142777 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099599873533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_22 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (4165377273693 / 5000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199203731407 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨22, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (4165377273693 / 5000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199203731407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_23 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41636597376183 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (219920772541 / 10000000000000 : ℝ))
      (E := (cell13150 ⟨23, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41636597376183 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (219920772541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_24 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41619434044297 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439842358113 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨24, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41619434044297 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439842358113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_25 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (20801141362557 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (274901969309 / 12500000000000 : ℝ))
      (E := (cell13150 ⟨25, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (20801141362557 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (274901969309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_26 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (129953573133 / 156250000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099609897493 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨26, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (129953573133 / 156250000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099609897493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_27 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41568016060643 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439844759517 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨27, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41568016060643 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439844759517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_28 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (16620360273381 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439845564571 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨28, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (16620360273381 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439845564571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_29 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83067594510319 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199231872713 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨29, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83067594510319 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199231872713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_30 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (8303341152003 / 10000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199235831737 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨30, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (8303341152003 / 10000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199235831737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_31 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (82999252364703 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (109961993849 / 5000000000000 : ℝ))
      (E := (cell13150 ⟨31, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (82999252364703 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (109961993849 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_32 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41482558506579 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439848778509 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨32, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41482558506579 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439848778509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_33 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41465502717189 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099623939683 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨33, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41465502717189 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099623939683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_34 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (82896917597501 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099625948401 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨34, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (82896917597501 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099625948401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_35 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41431426735911 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (219925594541 / 10000000000000 : ℝ))
      (E := (cell13150 ⟨35, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41431426735911 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (219925594541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_36 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (82828813026791 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199259966827 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨36, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (82828813026791 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199259966827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_37 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41397398116007 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199263961093 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨37, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41397398116007 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199263961093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_38 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (331043212229 / 400000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199267986767 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨38, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (331043212229 / 400000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199267986767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_39 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (8272683347241 / 10000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199271984751 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨39, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (8272683347241 / 10000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199271984751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13151_20 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (1042203815439 / 1250000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199084740899 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨20, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (1042203815439 / 1250000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199084740899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_21 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (8334190630673 / 10000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549772179019 / 25000000000000 : ℝ))
      (E := (cell13151 ⟨21, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (8334190630673 / 10000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549772179019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_22 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (16661506300237 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (137443297251 / 6250000000000 : ℝ))
      (E := (cell13151 ⟨22, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (16661506300237 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (137443297251 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_23 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (16654636157167 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099548373659 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨23, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (16654636157167 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099548373659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_24 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (416194270641 / 500000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199100809821 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨24, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (416194270641 / 500000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199100809821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_25 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83204551495967 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199104829559 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨25, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83204551495967 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199104829559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_26 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83170272856987 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099554404537 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨26, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83170272856987 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099554404537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_27 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (3325440727171 / 4000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199112809159 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨27, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (3325440727171 / 4000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199112809159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_28 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (20775446857753 / 25000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199116831961 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨28, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (20775446857753 / 25000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199116831961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_29 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41533790290269 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199120879397 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨29, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41533790290269 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199120879397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_30 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (20758349399089 / 25000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199124894601 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨30, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (20758349399089 / 25000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199124894601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_31 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (8299923844713 / 10000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099564439481 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨31, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (8299923844713 / 10000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099564439481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_32 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41482551550841 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (439826578449 / 20000000000000 : ℝ))
      (E := (cell13151 ⟨32, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41482551550841 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (439826578449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_33 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82930991528993 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (68723029233 / 3125000000000 : ℝ))
      (E := (cell13151 ⟨33, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82930991528993 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (68723029233 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_34 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82896903698203 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (87965638029 / 4000000000000 : ℝ))
      (E := (cell13151 ⟨34, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82896903698203 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (87965638029 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_35 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (16572567915721 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199144938541 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨35, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (16572567915721 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199144938541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_36 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82828799139651 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199148957861 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨36, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82828799139651 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199148957861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_37 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (16558956470189 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549788252199 / 25000000000000 : ℝ))
      (E := (cell13151 ⟨37, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (16558956470189 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549788252199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_38 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82760789182247 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199157032489 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨38, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82760789182247 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199157032489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_39 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82726819603469 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099580514269 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨39, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82726819603469 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099580514269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13152_20 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83376291252271 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099486883421 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨20, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83376291252271 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099486883421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_21 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (16668378466007 / 20000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198977797571 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨21, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (16668378466007 / 20000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198977797571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_22 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83307517530637 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (109949088821 / 5000000000000 : ℝ))
      (E := (cell13152 ⟨22, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83307517530637 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (109949088821 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_23 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83273166821429 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (274873227927 / 12500000000000 : ℝ))
      (E := (cell13152 ⟨23, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83273166821429 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (274873227927 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_24 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (20809710042483 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198989824873 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨24, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (20809710042483 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198989824873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_25 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83204537543831 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (439798768401 / 20000000000000 : ℝ))
      (E := (cell13152 ⟨25, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83204537543831 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (439798768401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_26 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83170258910977 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198997877423 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨26, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83170258910977 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198997877423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_27 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83136004239387 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099500937509 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨27, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83136004239387 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099500937509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_28 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (2077544337431 / 2500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (137437868461 / 6250000000000 : ℝ))
      (E := (cell13152 ⟨28, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (2077544337431 / 2500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (137437868461 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_29 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83067566652877 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (549752470471 / 25000000000000 : ℝ))
      (E := (cell13152 ⟨29, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83067566652877 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (549752470471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_30 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83033383674801 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099506947357 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨30, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83033383674801 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099506947357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_31 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (20749806132919 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099508967663 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨31, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (20749806132919 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099508967663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_32 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (20741272298081 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199021946351 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨32, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (20741272298081 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199021946351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_33 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41465488812863 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (43980519747 / 2000000000000 : ℝ))
      (E := (cell13152 ⟨33, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41465488812863 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (43980519747 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_34 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82896889801021 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (439806000091 / 20000000000000 : ℝ))
      (E := (cell13152 ⟨34, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82896889801021 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (439806000091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_35 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82862825687503 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (274879248269 / 12500000000000 : ℝ))
      (E := (cell13152 ⟨35, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82862825687503 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (274879248269 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_36 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (662630282037 / 800000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199038003399 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨36, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (662630282037 / 800000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199038003399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_37 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (8279476847199 / 10000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199042052307 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨37, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (8279476847199 / 10000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199042052307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_38 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82760775309357 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (109952303701 / 5000000000000 : ℝ))
      (E := (cell13152 ⟨38, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82760775309357 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (109952303701 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_39 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82726805736639 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (439810013627 / 20000000000000 : ℝ))
      (E := (cell13152 ⟨39, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82726805736639 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (439810013627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13153_20 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (81422145773 / 97656250000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198862846899 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨20, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (81422145773 / 97656250000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198862846899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_21 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83341878355467 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549716704129 / 25000000000000 : ℝ))
      (E := (cell13153 ⟨21, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83341878355467 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549716704129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_22 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (10413437945277 / 12500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198870850989 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨22, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (10413437945277 / 12500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198870850989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_23 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (1665463057183 / 2000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198874895309 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨23, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (1665463057183 / 2000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198874895309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_24 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83238826213789 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099439447069 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨24, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83238826213789 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099439447069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_25 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83204523593819 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (137430181793 / 6250000000000 : ℝ))
      (E := (cell13153 ⟨25, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83204523593819 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (137430181793 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_26 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83170244967091 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (219888694157 / 10000000000000 : ℝ))
      (E := (cell13153 ⟨26, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83170244967091 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (219888694157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_27 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83135990301621 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198890936677 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨27, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83135990301621 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198890936677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_28 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83101759565589 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099447477297 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨28, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83101759565589 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099447477297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_29 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83067552727337 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (137431183669 / 6250000000000 : ℝ))
      (E := (cell13153 ⟨29, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83067552727337 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (137431183669 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_30 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41516684877683 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (439780589837 / 20000000000000 : ℝ))
      (E := (cell13153 ⟨30, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41516684877683 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (439780589837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_31 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82999210618341 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198906987493 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨31, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82999210618341 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198906987493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_32 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82965075285083 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099455498131 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨32, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82965075285083 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099455498131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_33 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (3317238548983 / 4000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (43978300701 / 2000000000000 : ℝ))
      (E := (cell13153 ⟨33, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (3317238548983 / 4000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (43978300701 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_34 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16579375181191 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (219891904599 / 10000000000000 : ℝ))
      (E := (cell13153 ⟨34, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16579375181191 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (219891904599 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_35 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82862811798517 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198923029569 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨35, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82862811798517 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198923029569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_36 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82828771371713 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (439785408949 / 20000000000000 : ℝ))
      (E := (cell13153 ⟨36, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82828771371713 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (439785408949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_37 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82794754595147 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549732772907 / 25000000000000 : ℝ))
      (E := (cell13153 ⟨37, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82794754595147 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549732772907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_38 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82760761438579 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198935111361 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨38, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82760761438579 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198935111361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_39 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (1034084898399 / 1250000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274867387943 / 12500000000000 : ℝ))
      (E := (cell13153 ⟨39, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (1034084898399 / 1250000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274867387943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13154_20 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (521101645581 / 625000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198751922753 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨20, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (521101645581 / 625000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198751922753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_21 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83341864383027 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099377944801 / 50000000000000 : ℝ))
      (E := (cell13154 ⟨21, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83341864383027 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099377944801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_22 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (41653744797961 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099379960677 / 50000000000000 : ℝ))
      (E := (cell13154 ⟨22, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (41653744797961 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099379960677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_23 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (20818284724749 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198763963 / 100000000000 : ℝ))
      (E := (cell13154 ⟨23, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (20818284724749 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198763963 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_24 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (8323881225977 / 10000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099383979601 / 50000000000000 : ℝ))
      (E := (cell13154 ⟨24, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (8323881225977 / 10000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099383979601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_25 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (8320450964593 / 10000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549692992793 / 25000000000000 : ℝ))
      (E := (cell13154 ⟨25, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (8320450964593 / 10000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549692992793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_26 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83170231025327 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198776001519 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨26, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83170231025327 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198776001519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_27 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83135976365977 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198779994137 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨27, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83135976365977 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198779994137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_28 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (4155087281803 / 5000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198784009611 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨28, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (4155087281803 / 5000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198784009611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_29 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (20766884700979 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198788049861 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨29, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (20766884700979 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198788049861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_30 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (1660667116761 / 2000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439758411603 / 20000000000000 : ℝ))
      (E := (cell13154 ⟨30, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (1660667116761 / 2000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439758411603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_31 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82999196707123 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439759218809 / 20000000000000 : ℝ))
      (E := (cell13154 ⟨31, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82999196707123 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439759218809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_32 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (2074126534499 / 2500000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (109940005029 / 5000000000000 : ℝ))
      (E := (cell13154 ⟨32, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (2074126534499 / 2500000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (109940005029 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_33 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82930949825541 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549701019639 / 25000000000000 : ℝ))
      (E := (cell13154 ⟨33, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82930949825541 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549701019639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_34 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (20724215503251 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198808145983 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨34, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (20724215503251 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198808145983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_35 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (16572559582329 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549703031867 / 25000000000000 : ℝ))
      (E := (cell13154 ⟨35, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (16572559582329 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549703031867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_36 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (41414378745457 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549704035149 / 25000000000000 : ℝ))
      (E := (cell13154 ⟨36, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (41414378745457 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549704035149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_37 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82794740720417 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198820185477 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨37, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82794740720417 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198820185477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_38 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (10345093446239 / 12500000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198824203257 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨38, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (10345093446239 / 12500000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198824203257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_39 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (2585211812791 / 3125000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (219882819353 / 10000000000000 : ℝ))
      (E := (cell13154 ⟨39, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (2585211812791 / 3125000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (219882819353 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13155_20 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (83376249316497 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099320497201 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨20, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (83376249316497 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099320497201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_21 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41670925206357 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (219864501683 / 10000000000000 : ℝ))
      (E := (cell13155 ⟨21, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41670925206357 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (219864501683 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_22 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41653737815877 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439729809177 / 20000000000000 : ℝ))
      (E := (cell13155 ⟨22, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41653737815877 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439729809177 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_23 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (10409140617621 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (219865302649 / 10000000000000 : ℝ))
      (E := (cell13155 ⟨23, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (10409140617621 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (219865302649 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_24 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (20809699576969 / 25000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198657078481 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨24, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (20809699576969 / 25000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198657078481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_25 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (16640899140033 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198661087893 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨25, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (16640899140033 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198661087893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_26 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41585108542843 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198665115731 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨26, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41585108542843 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198665115731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_27 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (16627192486491 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439733821177 / 20000000000000 : ℝ))
      (E := (cell13155 ⟨27, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (16627192486491 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439733821177 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_28 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (83101731708651 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099336559471 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨28, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (83101731708651 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099336559471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_29 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (10383440610327 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (109933857841 / 5000000000000 : ℝ))
      (E := (cell13155 ⟨29, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (10383440610327 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (109933857841 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_30 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (20758335480713 / 25000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198681162651 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨30, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (20758335480713 / 25000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198681162651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_31 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (10374897849753 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099342598201 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨31, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (10374897849753 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099342598201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_32 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82965047476953 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099344600353 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨32, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82965047476953 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099344600353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_33 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41465467964311 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (137418323531 / 6250000000000 : ℝ))
      (E := (cell13155 ⟨33, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41465467964311 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (137418323531 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_34 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (10362106015271 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198697241783 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨34, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (10362106015271 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198697241783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_35 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82862784026887 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (87948048847 / 4000000000000 : ℝ))
      (E := (cell13155 ⟨35, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82862784026887 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (87948048847 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_36 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (20707185903057 / 25000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099352616129 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨36, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (20707185903057 / 25000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099352616129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_37 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82794726847799 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099354637569 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨37, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82794726847799 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099354637569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_38 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82760733703357 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198713290963 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨38, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82760733703357 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198713290963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_39 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41363382074407 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198717279329 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨39, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41363382074407 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198717279329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13156_20 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83376235342161 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219853012017 / 10000000000000 : ℝ))
      (E := (cell13156 ⟨20, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83376235342161 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219853012017 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_21 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83341836444527 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (137408383741 / 6250000000000 : ℝ))
      (E := (cell13156 ⟨21, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83341836444527 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (137408383741 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_22 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83307461669711 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (274817270777 / 12500000000000 : ℝ))
      (E := (cell13156 ⟨22, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83307461669711 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (274817270777 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_23 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (10409138873133 / 12500000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198542144171 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨23, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (10409138873133 / 12500000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198542144171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_24 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (16647756871621 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (54963654839 / 2500000000000 : ℝ))
      (E := (cell13156 ⟨24, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (16647756871621 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (54963654839 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_25 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83204481756523 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (68704693763 / 3125000000000 : ℝ))
      (E := (cell13156 ⟨25, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83204481756523 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (68704693763 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_26 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41585101574083 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439710845149 / 20000000000000 : ℝ))
      (E := (cell13156 ⟨26, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41585101574083 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439710845149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_27 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83135948501053 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549639553359 / 25000000000000 : ℝ))
      (E := (cell13156 ⟨27, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83135948501053 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549639553359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_28 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41550858891681 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198562224077 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨28, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41550858891681 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198562224077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_29 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41533755481717 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (17176298903 / 781250000000 : ℝ))
      (E := (cell13156 ⟨29, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41533755481717 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (17176298903 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_30 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83033328009773 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198570263091 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨30, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83033328009773 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198570263091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_31 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41499584445521 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439714858913 / 20000000000000 : ℝ))
      (E := (cell13156 ⟨31, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41499584445521 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439714858913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_32 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82965033576063 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099289148319 / 50000000000000 : ℝ))
      (E := (cell13156 ⟨32, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82965033576063 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099289148319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_33 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41465461016909 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198582328871 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨33, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41465461016909 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198582328871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_34 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41448417116723 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198586333393 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨34, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41448417116723 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198586333393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_35 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41431385072121 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099295184683 / 50000000000000 : ℝ))
      (E := (cell13156 ⟨35, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41431385072121 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099295184683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_36 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (16565745947131 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099297189213 / 50000000000000 : ℝ))
      (E := (cell13156 ⟨36, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (16565745947131 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099297189213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_37 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82794712977293 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219859836061 / 10000000000000 : ℝ))
      (E := (cell13156 ⟨37, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82794712977293 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219859836061 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_38 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (1293136247483 / 1562500000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099301216613 / 50000000000000 : ℝ))
      (E := (cell13156 ⟨38, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (1293136247483 / 1562500000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099301216613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_39 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41363375145213 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198606419707 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨39, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41363375145213 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198606419707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13157_20 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (2605506917811 / 3125000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274802405217 / 12500000000000 : ℝ))
      (E := (cell13157 ⟨20, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (2605506917811 / 3125000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274802405217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_21 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (83341822478467 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198423258681 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨21, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (83341822478467 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198423258681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_22 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (83307447709793 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198427282347 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨22, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (83307447709793 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198427282347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_23 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (20818274257821 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099215658023 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨23, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (20818274257821 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099215658023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_24 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41619385205229 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198435304441 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨24, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41619385205229 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198435304441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_25 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41602233907501 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198439308743 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨25, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41602233907501 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198439308743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_26 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (2599068412899 / 3125000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198443331563 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨26, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (2599068412899 / 3125000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198443331563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_27 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (20783983642943 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198447375277 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨27, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (20783983642943 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198447375277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_28 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (2596928245631 / 3125000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099225691763 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨28, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (2596928245631 / 3125000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099225691763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_29 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (83067497046371 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (137403463543 / 6250000000000 : ℝ))
      (E := (cell13157 ⟨29, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (83067497046371 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (137403463543 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_30 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (83033314098811 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (439691883579 / 20000000000000 : ℝ))
      (E := (cell13157 ⟨30, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (83033314098811 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (439691883579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_31 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (1296861796659 / 1562500000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198463447117 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨31, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (1296861796659 / 1562500000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198463447117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_32 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82965019677289 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099233723491 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨32, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82965019677289 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099233723491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_33 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (8293090814113 / 10000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099235738527 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨33, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (8293090814113 / 10000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099235738527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_34 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82896820346839 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198475479463 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨34, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82896820346839 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198475479463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_35 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (8286275626371 / 10000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274809939171 / 12500000000000 : ℝ))
      (E := (cell13157 ⟨35, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (8286275626371 / 10000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274809939171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_36 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41414357930597 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198483520407 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨36, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41414357930597 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198483520407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_37 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82794699108897 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274810944917 / 12500000000000 : ℝ))
      (E := (cell13157 ⟨37, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82794699108897 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274810944917 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_38 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41380352988289 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099245785651 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨38, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41380352988289 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099245785651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_39 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82726736434147 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099247777951 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨39, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82726736434147 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099247777951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13158_20 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (8337620739987 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198308417423 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨20, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (8337620739987 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198308417423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_21 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (20835452128633 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198312431651 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨21, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (20835452128633 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198312431651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_22 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (10413429219 / 12500000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198316452647 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨22, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (10413429219 / 12500000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198316452647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_23 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83273083079627 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198320483723 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨23, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83273083079627 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198320483723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_24 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83238756464933 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198324469541 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨24, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83238756464933 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198324469541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_25 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (20801113468901 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (137395529457 / 6250000000000 : ℝ))
      (E := (cell13158 ⟨25, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (20801113468901 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (137395529457 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_26 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83170175279491 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198332491647 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨26, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83170175279491 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198332491647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_27 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (8313592064461 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (549584133231 / 25000000000000 : ℝ))
      (E := (cell13158 ⟨27, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (8313592064461 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (549584133231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_28 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83101689939141 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099170269391 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨28, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83101689939141 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099170269391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_29 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (3322699325257 / 4000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198344569599 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨29, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (3322699325257 / 4000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198344569599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_30 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (41516650094983 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198348568507 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨30, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (41516650094983 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198348568507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_31 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (41499570541713 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198352595477 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨31, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (41499570541713 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198352595477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_32 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82965005780629 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (137397287071 / 6250000000000 : ℝ))
      (E := (cell13158 ⟨32, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82965005780629 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (137397287071 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_33 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (20732723562639 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (274795077631 / 12500000000000 : ℝ))
      (E := (cell13158 ⟨33, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (20732723562639 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (274795077631 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_34 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (10362100807793 / 12500000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439672924269 / 20000000000000 : ℝ))
      (E := (cell13158 ⟨34, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (10362100807793 / 12500000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439672924269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_35 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (8286274238529 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198368653183 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨35, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (8286274238529 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198368653183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_36 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (16565740397769 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (10991863291 / 500000000000 : ℝ))
      (E := (cell13158 ⟨36, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (16565740397769 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (10991863291 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_37 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82794685242613 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439675339031 / 20000000000000 : ℝ))
      (E := (cell13158 ⟨37, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82794685242613 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439675339031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_38 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82760692116353 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198380705193 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨38, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82760692116353 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198380705193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_39 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82726722579977 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099192373339 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨39, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82726722579977 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099192373339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13159_20 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83376193431913 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (137387349307 / 6250000000000 : ℝ))
      (E := (cell13159 ⟨20, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83376193431913 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (137387349307 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_21 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83341794552721 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (274775200053 / 12500000000000 : ℝ))
      (E := (cell13159 ⟨21, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83341794552721 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (274775200053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_22 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83307419796331 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (351712899 / 16000000000 : ℝ))
      (E := (cell13159 ⟨22, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83307419796331 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (351712899 / 16000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_23 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41636534565047 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198209647203 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨23, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41636534565047 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198209647203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_24 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83238742521531 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198213688859 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨24, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83238742521531 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198213688859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_25 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83204439938327 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549554422031 / 25000000000000 : ℝ))
      (E := (cell13159 ⟨25, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83204439938327 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549554422031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_26 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41585080674167 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198221705999 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨26, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41585080674167 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198221705999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_27 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (5195994169973 / 6250000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198225686377 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨27, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (5195994169973 / 6250000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198225686377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_28 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83101676020209 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198229748353 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨28, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83101676020209 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198229748353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_29 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41533734609299 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198233718317 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨29, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41533734609299 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198233718317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_30 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41516643141619 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549559443371 / 25000000000000 : ℝ))
      (E := (cell13159 ⟨30, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41516643141619 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549559443371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_31 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82999127182793 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (87929671929 / 4000000000000 : ℝ))
      (E := (cell13159 ⟨31, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82999127182793 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (87929671929 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_32 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (16592998377217 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (274780724213 / 12500000000000 : ℝ))
      (E := (cell13159 ⟨32, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (16592998377217 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (274780724213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_33 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (16586176072419 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198249819481 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨33, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (16586176072419 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198249819481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_34 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82896792579963 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (274781727211 / 12500000000000 : ℝ))
      (E := (cell13159 ⟨34, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82896792579963 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (274781727211 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_35 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82862728508983 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549564461871 / 25000000000000 : ℝ))
      (E := (cell13159 ⟨35, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82862728508983 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549564461871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_36 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41414344059303 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (439652370101 / 20000000000000 : ℝ))
      (E := (cell13159 ⟨36, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41414344059303 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (439652370101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_37 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41397335689219 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (219826588551 / 10000000000000 : ℝ))
      (E := (cell13159 ⟨37, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41397335689219 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (219826588551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_38 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82760678258237 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (439653978729 / 20000000000000 : ℝ))
      (E := (cell13159 ⟨38, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82760678258237 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (439653978729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_39 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (20681677181979 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198273933271 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨39, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (20681677181979 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198273933271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13160_20 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41688089733041 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198086814523 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨20, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41688089733041 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198086814523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_21 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (20835445148259 / 25000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198090823343 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨21, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (20835445148259 / 25000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198090823343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_22 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (16661481168557 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (87923793561 / 4000000000000 : ℝ))
      (E := (cell13160 ⟨22, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (16661481168557 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (87923793561 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_23 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (83273055182683 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198098864879 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨23, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (83273055182683 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198098864879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_24 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (332954914321 / 400000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (17172678481 / 781250000000 : ℝ))
      (E := (cell13160 ⟨24, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (332954914321 / 400000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (17172678481 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_25 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (8320442600317 / 10000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198106900743 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨25, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (8320442600317 / 10000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198106900743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_26 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (83170147419297 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099055458079 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨26, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (83170147419297 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099055458079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_27 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (16627178559329 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549528723531 / 25000000000000 : ℝ))
      (E := (cell13160 ⟨27, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (16627178559329 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549528723531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_28 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (16620332420679 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (274764861903 / 12500000000000 : ℝ))
      (E := (cell13160 ⟨28, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (16620332420679 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (274764861903 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_29 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (83067455307887 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099061460689 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨29, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (83067455307887 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099061460689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_30 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41516636189313 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198126974271 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨30, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41516636189313 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198126974271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_31 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41499556642137 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099065498393 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨31, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41499556642137 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099065498393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_32 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41482488996827 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549533747521 / 25000000000000 : ℝ))
      (E := (cell13160 ⟨32, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41482488996827 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549533747521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_33 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (20732716618937 / 25000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099069506863 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨33, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (20732716618937 / 25000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099069506863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_34 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41448389349847 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (439628601969 / 20000000000000 : ℝ))
      (E := (cell13160 ⟨34, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41448389349847 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (439628601969 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_35 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82862714634787 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2747683797 / 125000000000 : ℝ))
      (E := (cell13160 ⟨35, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82862714634787 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2747683797 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_36 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82828674250479 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (68692219957 / 3125000000000 : ℝ))
      (E := (cell13160 ⟨36, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82828674250479 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (68692219957 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_37 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82794657516373 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198155071681 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨37, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82794657516373 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198155071681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_38 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (8276066440223 / 10000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198159077913 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨38, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (8276066440223 / 10000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198159077913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_39 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41363347438981 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099081557841 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨39, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41363347438981 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099081557841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13161_20 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (10422020687797 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (68686751123 / 3125000000000 : ℝ))
      (E := (cell13161 ⟨20, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (10422020687797 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (68686751123 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_21 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41670883317737 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098990021033 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨21, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41670883317737 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098990021033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_22 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83307391891363 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197984055103 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨22, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83307391891363 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197984055103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_23 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (16654608247479 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197988078359 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨23, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (16654608247479 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197988078359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_24 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (8323871464109 / 10000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197992056497 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨24, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (8323871464109 / 10000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197992056497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_25 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41602206035067 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197996109167 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨25, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41602206035067 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197996109167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_26 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83170133492379 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (17584000977 / 800000000000 : ℝ))
      (E := (cell13161 ⟨26, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83170133492379 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (17584000977 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_27 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (259799621487 / 312500000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439600831233 / 20000000000000 : ℝ))
      (E := (cell13161 ⟨27, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (259799621487 / 312500000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439600831233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_28 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41550824094349 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198008154923 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨28, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41550824094349 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198008154923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_29 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83067441399293 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198012178781 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨29, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83067441399293 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198012178781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_30 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83033258476129 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (219801617087 / 10000000000000 : ℝ))
      (E := (cell13161 ⟨30, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83033258476129 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (219801617087 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_31 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (8299909938787 / 10000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099010095579 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨31, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (8299909938787 / 10000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099010095579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_32 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41482482051669 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (87920967291 / 4000000000000 : ℝ))
      (E := (cell13161 ⟨32, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41482482051669 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (87920967291 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_33 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41465426295757 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274753525473 / 12500000000000 : ℝ))
      (E := (cell13161 ⟨33, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41465426295757 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274753525473 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_34 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (82896764821537 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099016128233 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨34, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (82896764821537 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099016128233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_35 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41431350381351 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (549509070551 / 25000000000000 : ℝ))
      (E := (cell13161 ⟨35, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41431350381351 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (549509070551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_36 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (82828660384461 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198040281257 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨36, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (82828660384461 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198040281257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_37 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41397321828209 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (549511078097 / 25000000000000 : ℝ))
      (E := (cell13161 ⟨37, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41397321828209 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (549511078097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_38 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (20690162637083 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198048316741 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨38, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (20690162637083 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198048316741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_39 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (16545336206023 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198052352679 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨39, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (16545336206023 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198052352679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13162_20 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (41688075770397 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098932626577 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨20, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (41688075770397 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098932626577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_21 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20835438170009 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197869256593 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨21, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20835438170009 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197869256593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_22 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83307377942063 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197873266987 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨22, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83307377942063 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197873266987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_23 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20818256823557 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197877287647 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨23, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20818256823557 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197877287647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_24 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83238700704051 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (43957626433 / 2000000000000 : ℝ))
      (E := (cell13162 ⟨24, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83238700704051 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (43957626433 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_25 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (41602199069609 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (10989426567 / 500000000000 : ℝ))
      (E := (cell13162 ⟨25, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (41602199069609 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (10989426567 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_26 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (4158505978379 / 5000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197889382363 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨26, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (4158505978379 / 5000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197889382363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_27 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83135864957153 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (219789335553 / 10000000000000 : ℝ))
      (E := (cell13162 ⟨27, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83135864957153 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (219789335553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_28 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (41550817138059 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197897410433 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨28, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (41550817138059 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197897410433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_29 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (16613485498563 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197901373463 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨29, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (16613485498563 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197901373463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_30 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20758311143937 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197905421837 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨30, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20758311143937 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197905421837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_31 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (4149954274679 / 5000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197909439923 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨31, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (4149954274679 / 5000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197909439923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_32 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (41482475107567 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (439582685777 / 20000000000000 : ℝ))
      (E := (cell13162 ⟨32, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (41482475107567 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (439582685777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_33 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (5183177419337 / 6250000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (439583489657 / 20000000000000 : ℝ))
      (E := (cell13162 ⟨33, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (5183177419337 / 6250000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (439583489657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_34 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82896750945491 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (274740187363 / 12500000000000 : ℝ))
      (E := (cell13162 ⟨34, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82896750945491 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (274740187363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_35 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (10357835861591 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (34342586291 / 1562500000000 : ℝ))
      (E := (cell13162 ⟨35, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (10357835861591 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (34342586291 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_36 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82828646520553 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (549482379927 / 25000000000000 : ℝ))
      (E := (cell13162 ⟨36, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82828646520553 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (549482379927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_37 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82794629798571 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (439586709783 / 20000000000000 : ℝ))
      (E := (cell13162 ⟨37, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82794629798571 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (439586709783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_38 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82760636696541 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (219793755139 / 10000000000000 : ℝ))
      (E := (cell13162 ⟨38, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82760636696541 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (219793755139 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_39 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (10340833398047 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (274742698187 / 12500000000000 : ℝ))
      (E := (cell13162 ⟨39, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (10340833398047 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (274742698187 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13163_20 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (10422017197667 / 12500000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197754524497 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨20, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (10422017197667 / 12500000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197754524497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_21 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83341738726721 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (219775852527 / 10000000000000 : ℝ))
      (E := (cell13163 ⟨21, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83341738726721 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (219775852527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_22 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (16661472798977 / 20000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (439552506609 / 20000000000000 : ℝ))
      (E := (cell13163 ⟨22, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (16661472798977 / 20000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (439552506609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_23 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83273013353183 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (549441637783 / 25000000000000 : ℝ))
      (E := (cell13163 ⟨23, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83273013353183 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (549441637783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_24 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (20809671692283 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (219777058261 / 10000000000000 : ℝ))
      (E := (cell13163 ⟨24, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (20809671692283 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (219777058261 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_25 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83204384210421 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (54944364297 / 2500000000000 : ℝ))
      (E := (cell13163 ⟨25, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83204384210421 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (54944364297 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_26 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83170105644899 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197778638411 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨26, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83170105644899 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197778638411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_27 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (10391981380073 / 12500000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197782609189 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨27, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (10391981380073 / 12500000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197782609189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_28 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (16620324073131 / 20000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197786661753 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨28, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (16620324073131 / 20000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197786661753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_29 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83067413588453 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098895340511 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨29, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83067413588453 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098895340511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_30 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41516615338741 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (439558933723 / 20000000000000 : ℝ))
      (E := (cell13163 ⟨30, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41516615338741 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (439558933723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_31 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (20749767900351 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197798684501 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨31, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (20749767900351 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197798684501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_32 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (20741234082261 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197802729911 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨32, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (20741234082261 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197802729911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_33 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41465412414691 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098903373613 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨33, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41465412414691 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098903373613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_34 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82896737071557 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (549452684289 / 25000000000000 : ℝ))
      (E := (cell13163 ⟨34, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82896737071557 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (549452684289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_35 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (2589458532027 / 3125000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197814758861 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨35, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (2589458532027 / 3125000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197814758861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_36 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41414316329377 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (87912750159 / 4000000000000 : ℝ))
      (E := (cell13163 ⟨36, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41414316329377 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (87912750159 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_37 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (5174663496427 / 6250000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197822781259 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨37, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (5174663496427 / 6250000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197822781259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_38 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82760622846857 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098913420301 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨38, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82760622846857 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098913420301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_39 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41363326670371 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197830814133 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨39, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41363326670371 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197830814133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13164_20 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41688061812001 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098821895823 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨20, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41688061812001 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098821895823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_21 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (10417715596941 / 12500000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (439529557951 / 20000000000000 : ℝ))
      (E := (cell13164 ⟨21, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (10417715596941 / 12500000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (439529557951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_22 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83307350049829 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197651853281 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨22, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83307350049829 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197651853281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_23 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41636499707129 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197655868819 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨23, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41636499707129 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197655868819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_24 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83238672836333 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197659839379 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨24, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83238672836333 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197659839379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_25 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41602185141871 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197663884611 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨25, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41602185141871 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197663884611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_26 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83170091724337 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (549416972567 / 25000000000000 : ℝ))
      (E := (cell13164 ⟨26, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83170091724337 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (549416972567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_27 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20783959281533 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (549417979287 / 25000000000000 : ℝ))
      (E := (cell13164 ⟨27, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20783959281533 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (549417979287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_28 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83101606457307 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197675908887 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨28, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83101606457307 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197675908887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_29 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41533699843103 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098839962931 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨29, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41533699843103 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098839962931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_30 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83033216781329 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098841984883 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨30, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83033216781329 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098841984883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_31 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41499528855671 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098843991737 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨31, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41499528855671 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098843991737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_32 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41482461222533 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197691968151 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨32, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41482461222533 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197691968151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_33 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82930810951483 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197695983359 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨33, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82930810951483 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197695983359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_34 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82896723199733 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098850014939 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨34, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82896723199733 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098850014939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_35 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82862659159109 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197704049591 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨35, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82862659159109 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197704049591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_36 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82828618799063 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197708042761 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨36, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82828618799063 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197708042761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_37 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82794602089201 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (439542413629 / 20000000000000 : ℝ))
      (E := (cell13164 ⟨37, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82794602089201 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (439542413629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_38 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82760608999281 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (219771606689 / 10000000000000 : ℝ))
      (E := (cell13164 ⟨38, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82760608999281 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (219771606689 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_39 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (16545327899843 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197720097359 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨39, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (16545327899843 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197720097359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13165_20 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83376109668791 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197533112923 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨20, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83376109668791 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197533112923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_21 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (41670855413229 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197537108391 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨21, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (41670855413229 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197537108391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_22 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (16661467221379 / 20000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197541110953 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨22, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (16661467221379 / 20000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197541110953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_23 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83272985477453 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098772561961 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨23, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83272985477453 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098772561961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_24 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (41619329452827 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549387287593 / 25000000000000 : ℝ))
      (E := (cell13165 ⟨24, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (41619329452827 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549387287593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_25 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83204356359183 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (43951063863 / 2000000000000 : ℝ))
      (E := (cell13165 ⟨25, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83204356359183 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (43951063863 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_26 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83170077805891 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197557196401 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨26, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83170077805891 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197557196401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_27 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (20783955803449 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098780610459 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨27, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (20783955803449 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098780610459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_28 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (20775398137769 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197565210341 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨28, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (20775398137769 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197565210341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_29 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83067385786073 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197569225049 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨29, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83067385786073 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197569225049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_30 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (8303320288729 / 10000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (219757326673 / 10000000000000 : ℝ))
      (E := (cell13165 ⟨30, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (8303320288729 / 10000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (219757326673 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_31 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (2593720119481 / 3125000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098788639131 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨31, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (2593720119481 / 3125000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098788639131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_32 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (12963266963 / 15625000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197581319413 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨32, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (12963266963 / 15625000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197581319413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_33 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (5183174817231 / 6250000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197585332561 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨33, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (5183174817231 / 6250000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197585332561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_34 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82896709330019 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (137349332401 / 6250000000000 : ℝ))
      (E := (cell13165 ⟨34, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82896709330019 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (137349332401 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_35 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82862645295463 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (109879666807 / 5000000000000 : ℝ))
      (E := (cell13165 ⟨35, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82862645295463 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (109879666807 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_36 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82828604941481 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098798693031 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨36, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82828604941481 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098798693031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_37 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82794588237677 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197601350851 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨37, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82794588237677 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197601350851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_38 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (8276059515381 / 10000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197605406489 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨38, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (8276059515381 / 10000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197605406489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_39 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82726625659793 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (87904377407 / 4000000000000 : ℝ))
      (E := (cell13165 ⟨39, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82726625659793 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (87904377407 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13166_20 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41688047857851 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197422430009 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨20, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41688047857851 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197422430009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_21 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83341696879509 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197426422837 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨21, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83341696879509 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197426422837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_22 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (260335381769 / 312500000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (274678810147 / 12500000000000 : ℝ))
      (E := (cell13166 ⟨22, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (260335381769 / 312500000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (274678810147 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_23 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (5204560721423 / 6250000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197434491621 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨23, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (5204560721423 / 6250000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197434491621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_24 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83238644977093 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (439487703119 / 20000000000000 : ℝ))
      (E := (cell13166 ⟨24, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83238644977093 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (439487703119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_25 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83204342436741 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098721248751 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨25, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83204342436741 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098721248751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_26 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83170063889563 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098723249173 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨26, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83170063889563 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098723249173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_27 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (10391976162947 / 12500000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197450520503 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨27, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (10391976162947 / 12500000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197450520503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_28 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83101578646959 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098727283061 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨28, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83101578646959 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098727283061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_29 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (16613474377611 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (439491715717 / 20000000000000 : ℝ))
      (E := (cell13166 ⟨29, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (16613474377611 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (439491715717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_30 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (16606637799073 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197462559511 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨30, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (16606637799073 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197462559511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_31 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41499514968777 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197466627449 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨31, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41499514968777 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197466627449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_32 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (16592978936689 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197470607891 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨32, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (16592978936689 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197470607891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_33 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (82930783202019 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (549368654739 / 25000000000000 : ℝ))
      (E := (cell13166 ⟨33, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (82930783202019 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (549368654739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_34 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41448347731207 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197478661427 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨34, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41448347731207 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197478661427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_35 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41431315716963 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197482677183 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨35, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41431315716963 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197482677183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_36 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41414295543003 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (274685833311 / 12500000000000 : ℝ))
      (E := (cell13166 ⟨36, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41414295543003 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (274685833311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_37 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (4139728719413 / 5000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197490688101 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨37, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (4139728719413 / 5000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197490688101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_38 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41380290655223 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197494741911 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨38, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41380290655223 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197494741911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_39 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (20681652955619 / 25000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (68671834689 / 3125000000000 : ℝ))
      (E := (cell13166 ⟨39, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (20681652955619 / 25000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (68671834689 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13167_20 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (651375638787 / 781250000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197311742901 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨20, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (651375638787 / 781250000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197311742901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_21 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83341682934681 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098657895719 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨21, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83341682934681 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098657895719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_22 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41653654113693 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098659894419 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨22, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41653654113693 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098659894419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_23 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83272957610203 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (8583296081 / 390625000000 : ℝ))
      (E := (cell13167 ⟨23, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83272957610203 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (8583296081 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_24 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83238631050651 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197327818211 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨24, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83238631050651 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197327818211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_25 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (1300067633069 / 1562500000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098665928053 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨25, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (1300067633069 / 1562500000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098665928053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_26 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83170049975351 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197335854567 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨26, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83170049975351 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197335854567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_27 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (5195987212217 / 6250000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (549334968597 / 25000000000000 : ℝ))
      (E := (cell13167 ⟨27, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (5195987212217 / 6250000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (549334968597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_28 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83101564744957 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197343917717 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨28, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83101564744957 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197343917717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_29 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (1661347159843 / 2000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (17166780687 / 781250000000 : ℝ))
      (E := (cell13167 ⟨29, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (1661347159843 / 2000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (17166780687 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_30 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (5189573444097 / 6250000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439470381333 / 20000000000000 : ℝ))
      (E := (cell13167 ⟨30, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (5189573444097 / 6250000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439470381333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_31 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (20749754013457 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (137334744617 / 6250000000000 : ℝ))
      (E := (cell13167 ⟨31, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (20749754013457 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (137334744617 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_32 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82964880805801 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (219735995079 / 10000000000000 : ℝ))
      (E := (cell13167 ⟨32, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82964880805801 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (219735995079 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_33 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82930769330451 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098681979899 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨33, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82930769330451 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098681979899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_34 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41448340798459 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (8583468751 / 390625000000 : ℝ))
      (E := (cell13167 ⟨34, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41448340798459 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (8583468751 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_35 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82862617574497 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197372014047 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨35, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82862617574497 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197372014047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_36 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82828577232639 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (274672000179 / 12500000000000 : ℝ))
      (E := (cell13167 ⟨36, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82828577232639 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (274672000179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_37 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82794560540949 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197380021173 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨37, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82794560540949 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197380021173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_38 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41380283734593 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (549346018289 / 25000000000000 : ℝ))
      (E := (cell13167 ⟨38, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41380283734593 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (549346018289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_39 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82726597987263 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197388098281 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨39, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82726597987263 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197388098281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13168_20 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83376067815891 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098600554963 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨20, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83376067815891 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098600554963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_21 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41670834495987 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (274650644481 / 12500000000000 : ℝ))
      (E := (cell13168 ⟨21, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41670834495987 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (274650644481 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_22 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20826823572703 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (54930228767 / 2500000000000 : ℝ))
      (E := (cell13168 ⟨22, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20826823572703 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (54930228767 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_23 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20818235919939 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197213156057 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨23, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20818235919939 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197213156057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_24 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41619308563163 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098608587529 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨24, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41619308563163 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098608587529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_25 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83204314598209 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549305302631 / 25000000000000 : ℝ))
      (E := (cell13168 ⟨25, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83204314598209 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549305302631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_26 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (16634007212651 / 20000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197225206603 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨26, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (16634007212651 / 20000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197225206603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_27 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83135781489483 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (274653653011 / 12500000000000 : ℝ))
      (E := (cell13168 ⟨27, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83135781489483 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (274653653011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_28 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (8310155084507 / 10000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197233265127 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨28, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (8310155084507 / 10000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197233265127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_29 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41533672049179 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (439447454621 / 20000000000000 : ℝ))
      (E := (cell13168 ⟨29, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41533672049179 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (439447454621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_30 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20758290304463 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098620654097 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨30, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20758290304463 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098620654097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_31 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41499501086107 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (87889812531 / 4000000000000 : ℝ))
      (E := (cell13168 ⟨31, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41499501086107 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (87889812531 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_32 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20741216732567 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (137328084257 / 6250000000000 : ℝ))
      (E := (cell13168 ⟨32, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20741216732567 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (137328084257 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_33 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41465377730497 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098626677543 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨33, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41465377730497 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098626677543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_34 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20724166933383 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098628667453 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨34, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20724166933383 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098628667453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_35 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (10357825464647 / 12500000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197261346733 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨35, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (10357825464647 / 12500000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197261346733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_36 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82828563381379 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197265390897 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨36, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82828563381379 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197265390897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_37 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (1293664792121 / 1562500000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (219726940879 / 10000000000000 : ℝ))
      (E := (cell13168 ⟨37, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (1293664792121 / 1562500000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (219726940879 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_38 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (5172534601877 / 6250000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098636700113 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨38, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (5172534601877 / 6250000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098636700113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_39 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41363292077077 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549319355893 / 25000000000000 : ℝ))
      (E := (cell13168 ⟨39, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41363292077077 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549319355893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13169_20 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83376053869167 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098545265543 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨20, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83376053869167 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098545265543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_21 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (20835413762847 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (219709451607 / 10000000000000 : ℝ))
      (E := (cell13169 ⟨21, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (20835413762847 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (219709451607 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_22 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83307280356357 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439419713341 / 20000000000000 : ℝ))
      (E := (cell13169 ⟨22, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83307280356357 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439419713341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_23 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83272929751427 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098551284793 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨23, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83272929751427 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098551284793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_24 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83238603204119 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439421317227 / 20000000000000 : ℝ))
      (E := (cell13169 ⟨24, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83238603204119 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439421317227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_25 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83204300682117 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098555280379 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨25, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83204300682117 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098555280379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_26 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (3326800886131 / 4000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098557306459 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨26, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (3326800886131 / 4000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098557306459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_27 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (10391970948201 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (549279657023 / 25000000000000 : ℝ))
      (E := (cell13169 ⟨27, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (10391970948201 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (549279657023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_28 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (16620307389459 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098561304179 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨28, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (16620307389459 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098561304179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_29 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (2076683255167 / 2500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098563336313 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨29, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (2076683255167 / 2500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098563336313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_30 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83033147332263 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197130646987 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨30, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83033147332263 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197130646987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_31 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82998988292711 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098567354249 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨31, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82998988292711 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098567354249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_32 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (20741213264211 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197138682653 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨32, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (20741213264211 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197138682653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_33 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (16586148318729 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197142746199 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨33, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (16586148318729 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197142746199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_34 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82896653872253 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197146724031 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨34, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82896653872253 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197146724031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_35 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (41431294930981 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098575366959 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨35, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (41431294930981 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098575366959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_36 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (1294196086441 / 1562500000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197154776189 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨36, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (1294196086441 / 1562500000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197154776189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_37 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (20698633213161 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197158792233 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨37, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (20698633213161 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197158792233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_38 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (41380269896491 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (549290695467 / 25000000000000 : ℝ))
      (E := (cell13169 ⟨38, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (41380269896491 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (549290695467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_39 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82726570323149 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197166803457 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨39, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82726570323149 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197166803457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13170_20 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83376039924563 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196979889733 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨20, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83376039924563 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196979889733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_21 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (2083541027823 / 2500000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196983930451 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨21, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (2083541027823 / 2500000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196983930451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_22 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83307266424021 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549246980043 / 25000000000000 : ℝ))
      (E := (cell13170 ⟨22, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83307266424021 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549246980043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_23 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83272915825217 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098495989463 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨23, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83272915825217 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098495989463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_24 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (20809647321007 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196995993027 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨24, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (20809647321007 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196995993027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_25 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41602143384071 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439399993049 / 20000000000000 : ℝ))
      (E := (cell13170 ⟨25, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41602143384071 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439399993049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_26 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (8317000824541 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197004015049 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨26, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (8317000824541 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197004015049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_27 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83135753683847 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197008027913 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨27, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83135753683847 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197008027913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_28 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41550761525817 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (87880482577 / 4000000000000 : ℝ))
      (E := (cell13170 ⟨28, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41550761525817 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (87880482577 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_29 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83067316317113 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439403213593 / 20000000000000 : ℝ))
      (E := (cell13170 ⟨29, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83067316317113 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439403213593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_30 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41516566724393 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439404008031 / 20000000000000 : ℝ))
      (E := (cell13170 ⟨30, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41516566724393 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439404008031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_31 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82998974415317 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098512049771 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨31, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82998974415317 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098512049771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_32 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (8296483918553 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098514065111 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨32, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (8296483918553 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098514065111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_33 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (16586145545681 / 20000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197032133131 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨33, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (16586145545681 / 20000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197032133131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_34 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82896640013081 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197036108979 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨34, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82896640013081 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197036108979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_35 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (16572515201771 / 20000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197040175599 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨35, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (16572515201771 / 20000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197040175599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_36 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (10353566960647 / 12500000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098522078651 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨36, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (10353566960647 / 12500000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098522078651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_37 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (1655890380233 / 2000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (4394096343 / 200000000000 : ℝ))
      (E := (cell13170 ⟨37, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (1655890380233 / 2000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (4394096343 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_38 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (20690131489509 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197052218079 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨38, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (20690131489509 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197052218079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_39 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82726556494247 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098528118969 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨39, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82726556494247 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098528118969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13171_20 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (130275040597 / 156250000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439373860503 / 20000000000000 : ℝ))
      (E := (cell13171 ⟨20, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (130275040597 / 156250000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439373860503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_21 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (20835406794143 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439374668129 / 20000000000000 : ℝ))
      (E := (cell13171 ⟨21, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (20835406794143 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439374668129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_22 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83307252493803 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098438693097 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨22, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83307252493803 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098438693097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_23 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83272901901123 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (549220346021 / 25000000000000 : ℝ))
      (E := (cell13171 ⟨23, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83272901901123 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (549220346021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_24 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41619287683027 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439377079147 / 20000000000000 : ℝ))
      (E := (cell13171 ⟨24, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41619287683027 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439377079147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_25 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41602136428141 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196889423991 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨25, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41602136428141 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196889423991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_26 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83169994339659 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098446706499 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨26, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83169994339659 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098446706499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_27 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (415678698921 / 500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196897423553 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨27, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (415678698921 / 500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196897423553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_28 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41550754579043 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196901457801 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨28, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41550754579043 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196901457801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_29 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41533651214829 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098452729563 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨29, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41533651214829 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098452729563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_30 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (4151655978371 / 5000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196909487701 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨30, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (4151655978371 / 5000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196909487701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_31 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41499480270017 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274614185801 / 12500000000000 : ℝ))
      (E := (cell13171 ⟨31, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41499480270017 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274614185801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_32 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (3318593012653 / 4000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196917515011 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨32, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (3318593012653 / 4000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196917515011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_33 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82930713865273 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (137307594743 / 6250000000000 : ℝ))
      (E := (cell13171 ⟨33, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82930713865273 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (137307594743 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_34 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82896626156017 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196925548403 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨34, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82896626156017 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196925548403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_35 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41431281078927 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196929554433 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨35, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41431281078927 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196929554433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_36 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (10353565230029 / 12500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196933592943 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨36, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (10353565230029 / 12500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196933592943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_37 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82794505172759 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196937605317 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨37, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82794505172759 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196937605317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_38 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82760512125193 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (54923541253 / 2500000000000 : ℝ))
      (E := (cell13171 ⟨38, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82760512125193 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (54923541253 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_39 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82726542667447 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274618208531 / 12500000000000 : ℝ))
      (E := (cell13171 ⟨39, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82726542667447 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274618208531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13172_20 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (20844003010429 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098379384717 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨20, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (20844003010429 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098379384717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_21 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83341613242343 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196762804999 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨21, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83341613242343 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196762804999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_22 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41653619282851 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196766789661 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨22, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41653619282851 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196766789661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_23 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83272887979147 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274596355431 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨23, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83272887979147 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274596355431 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_24 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (20809640362549 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (87870994107 / 4000000000000 : ℝ))
      (E := (cell13172 ⟨24, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (20809640362549 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (87870994107 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_25 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41602129473269 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274597359819 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨25, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41602129473269 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274597359819 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_26 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41584990218011 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196782865229 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨26, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41584990218011 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196782865229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_27 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83135725886667 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196786873497 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨27, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83135725886667 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196786873497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_28 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (1662029905333 / 2000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196790905507 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨28, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (1662029905333 / 2000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196790905507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_29 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (16613457708863 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196794904639 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨29, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (16613457708863 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196794904639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_30 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83033105688163 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (219679893107 / 10000000000000 : ℝ))
      (E := (cell13172 ⟨30, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83033105688163 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (219679893107 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_31 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (4149947333343 / 5000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (549200731919 / 25000000000000 : ℝ))
      (E := (cell13172 ⟨31, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (4149947333343 / 5000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (549200731919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_32 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (20741202862307 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098403477113 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨32, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (20741202862307 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098403477113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_33 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (10366337500531 / 12500000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (87872440469 / 4000000000000 : ℝ))
      (E := (cell13172 ⟨33, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (10366337500531 / 12500000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (87872440469 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_34 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (4144830615053 / 5000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196814983649 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨34, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (4144830615053 / 5000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196814983649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_35 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41431274154479 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196818987767 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨35, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41431274154479 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196818987767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_36 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41414253998697 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196823024407 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨36, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41414253998697 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196823024407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_37 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82794491335973 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (27460337937 / 1250000000000 : ℝ))
      (E := (cell13172 ⟨37, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82794491335973 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (27460337937 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_38 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41380249147227 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196831077987 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨38, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41380249147227 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196831077987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_39 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82726528842749 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196835094387 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨39, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82726528842749 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196835094387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13173_20 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (5210999881467 / 6250000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196648232167 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨20, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (5210999881467 / 6250000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196648232167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_21 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (10417699913779 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196652265169 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨21, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (10417699913779 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196652265169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_22 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (83307224639719 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098328123657 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨22, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (83307224639719 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098328123657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_23 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (41636437029643 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196660298631 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨23, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (41636437029643 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196660298631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_24 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (41619273768227 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196664305433 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨24, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (41619273768227 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196664305433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_25 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (83204245038907 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098334164467 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨25, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (83204245038907 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098334164467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_26 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (83169966534499 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (6864600979 / 312500000000 : ℝ))
      (E := (cell13173 ⟨26, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (83169966534499 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (6864600979 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_27 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (16627142398249 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439335263853 / 20000000000000 : ℝ))
      (E := (cell13173 ⟨27, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (16627142398249 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439335263853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_28 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (41550740688663 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439336069807 / 20000000000000 : ℝ))
      (E := (cell13173 ⟨28, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (41550740688663 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439336069807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_29 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (41533637330541 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219668440451 / 10000000000000 : ℝ))
      (E := (cell13173 ⟨29, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (41533637330541 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219668440451 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_30 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (83033091811017 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098344185131 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨30, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (83033091811017 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098344185131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_31 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (16599786559159 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196692423351 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨31, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (16599786559159 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196692423351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_32 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (1037059969803 / 1250000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219669644787 / 10000000000000 : ℝ))
      (E := (cell13173 ⟨32, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (1037059969803 / 1250000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219669644787 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_33 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82930686145331 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196700444759 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨33, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82930686145331 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196700444759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_34 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82896598448209 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (17573635787 / 800000000000 : ℝ))
      (E := (cell13173 ⟨34, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82896598448209 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (17573635787 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_35 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (10357816807771 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196708475603 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨35, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (10357816807771 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196708475603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_36 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (4141424707833 / 5000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1372945319 / 62500000000 : ℝ))
      (E := (cell13173 ⟨36, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (4141424707833 / 5000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1372945319 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_37 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (8279447750129 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439343303831 / 20000000000000 : ℝ))
      (E := (cell13173 ⟨37, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (8279447750129 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439343303831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_38 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82760484465817 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196720560431 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨38, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82760484465817 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196720560431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_39 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82726515020153 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098362287563 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨39, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82726515020153 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098362287563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13174_20 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41687992083673 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (549134422679 / 25000000000000 : ℝ))
      (E := (cell13174 ⟨20, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41687992083673 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (549134422679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_21 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83341585380239 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098270860577 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨21, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83341585380239 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098270860577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_22 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83307210715853 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098272879577 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨22, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83307210715853 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098272879577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_23 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41636430070771 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (17160544919 / 781250000000 : ℝ))
      (E := (cell13174 ⟨23, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41636430070771 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (17160544919 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_24 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41619266812413 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196553754011 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨24, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41619266812413 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196553754011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_25 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83204231133391 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439311555027 / 20000000000000 : ℝ))
      (E := (cell13174 ⟨25, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83204231133391 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439311555027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_26 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83169952635089 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098280907807 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨26, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83169952635089 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098280907807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_27 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (5195981131121 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (109828290967 / 5000000000000 : ℝ))
      (E := (cell13174 ⟨27, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (5195981131121 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (109828290967 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_28 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (1298460429533 / 1562500000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196569846897 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨28, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (1298460429533 / 1562500000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196569846897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_29 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83067260779959 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196573841671 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨29, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83067260779959 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196573841671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_30 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (4151653896799 / 5000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439315572767 / 20000000000000 : ℝ))
      (E := (cell13174 ⟨30, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (4151653896799 / 5000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439315572767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_31 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82998918926839 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196581914849 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨31, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82998918926839 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196581914849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_32 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82964783721359 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196585937341 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨32, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82964783721359 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196585937341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_33 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (2073266807213 / 2500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (274573741531 / 12500000000000 : ℝ))
      (E := (cell13174 ⟨33, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (2073266807213 / 2500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (274573741531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_34 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82896584597463 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196593958929 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨34, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82896584597463 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196593958929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_35 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82862520617483 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196597959267 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨35, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82862520617483 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196597959267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_36 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82828480318029 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098300996111 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨36, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82828480318029 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098300996111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_37 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82794463668709 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (109830299959 / 5000000000000 : ℝ))
      (E := (cell13174 ⟨37, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82794463668709 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (109830299959 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_38 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41380235319641 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439322007741 / 20000000000000 : ℝ))
      (E := (cell13174 ⟨38, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41380235319641 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439322007741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_39 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41363250599829 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (137288378231 / 6250000000000 : ℝ))
      (E := (cell13174 ⟨39, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41363250599829 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (137288378231 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

end BstLean.Part268
